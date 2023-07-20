use std::sync::{Arc, Mutex};
use std::fs::File;
use std::io::{self, Write};
use rand::distributions::{Alphanumeric, DistString};
use ring::rand::{SystemRandom, SecureRandom};
use rand::Rng;
use rug::Integer;
use num_primes::Generator;
use std::collections::HashMap;
use std::time::SystemTime;
use csv::{ReaderBuilder, Writer};
use rsa::{Pkcs1v15Encrypt, RsaPrivateKey, RsaPublicKey};
use actix_web::{get, App, HttpResponse, HttpServer};
use serde_json::json;

#[derive(Debug, Clone)]
pub struct Txn {
    commitment_value: String,
    blinding_factor: String,
}

#[derive(Debug, Clone)]
pub struct TxnData {
    timestamp: Integer,
    account_data: HashMap<u64, Txn>,
}

impl Txn {
    pub fn clone(&self) -> Self {
        Self {
            commitment_value: self.commitment_value.clone(),
            blinding_factor: self.blinding_factor.clone(),
        }
    }
}

async fn add_file() -> Result<(String, String), Box<dyn std::error::Error>> {
    print!("\nEnter the auth token: ");
    let mut input = String::new();
    io::stdout().flush()?;
    io::stdin().read_line(&mut input)?;
    let auth_token = input.trim();
    let password = Alphanumeric.sample_string(&mut rand::thread_rng(), 32);
    println!("{}", password);
    let cid_result = w3s::helper::upload (
        "data.csv",
        auth_token,
        2,
        Some(Arc::new(Mutex::new(|name, part, pos, total| {
            println!("name: {name} part:{part} {pos}/{total}");
        }))),
        Some(None),
        Some(password.as_bytes().to_vec()),
        Some(None),
        )
        .await?;

    Ok((cid_result[0].to_string(), password))
}

async fn retrieve_file(cid: String, password: String) -> Result<(), Box<dyn std::error::Error>> {
    let mut file = File::create("data.csv")?;
    let url = format!("https://{}.ipfs.w3s.link/data.csv", cid);
    let name = "data";
    w3s::helper::download(
        url,
        name,
        &mut file,
        Some(Arc::new(Mutex::new(|name, _, pos, total| {
            println!("name: {name} {pos}/{total}");
        }))),
        None,
        Some(password.as_bytes().to_vec()),
        true,
        )
        .await?;

    Ok(())
}

fn generate_values() -> (Integer, Integer, Integer) {
    println!("\nGenerating values...\n");
    let rand = SystemRandom::new();
    let p = Integer::from_str_radix(&Generator::safe_prime(256).to_string(), 10).unwrap();
    let q: Integer = (p.clone() - Integer::from(1)) / 2;
    let mut a;
    let mut g;
    loop {
        a = random_integer(&rand, Integer::from(0), p.clone()).pow_mod(&Integer::from(1), &p).unwrap();
        g = a.pow_mod(&((p.clone() - 1) / q.clone()), &p).unwrap(); 
        if g != 1 {
            break;
        }
    }
    let h = g.clone().pow_mod(&random_integer(&rand, Integer::from(0), p.clone()), &p).unwrap();
    (g, h, p)
}

fn commit_value(x: Integer, g: Integer, h: Integer, p: Integer) -> (Integer, Integer) {
    let rand = SystemRandom::new();
    let r = random_integer(&rand, Integer::from(0), (p.clone() - Integer::from(1)) / 2);
    let c = (g.clone().pow_mod(&x, &p).unwrap() * h.pow_mod(&r, &p).unwrap()) % p.clone();
    (c, r)
}

fn verify_commitment(c: Integer, g: Integer, h: Integer, x: Integer, r: Integer, p: Integer) -> bool {
    let c1 = (g.clone().pow_mod(&x, &p).unwrap() * h.pow_mod(&r, &p).unwrap()) % p.clone();
    c1 == c
}

fn random_integer(rng: &SystemRandom, lower_limit: Integer, upper_limit: Integer) -> Integer {
    loop {
        let mut bytes = vec![0; ((upper_limit.significant_bits() + 7) / 8) as usize];
        rng.fill(&mut bytes).unwrap();
        let num = Integer::from_digits(&bytes, rug::integer::Order::Lsf);
        if num > lower_limit && num < upper_limit {
            return num;
        }
    }
}

fn transact(timestamp: Integer, sender: u64, send_amt: u64, receiver: u64, receive_amt: u64, g: Integer, h: Integer, p: Integer, keys: Vec<(RsaPrivateKey, RsaPublicKey)>, number_of_accounts: u64, funds: &mut Vec<u64>, sums_blinding: &mut Vec<Integer>, txns: &mut Vec<TxnData>) {
    println!("\nAccount {sender} attempts to send {send_amt} CBDC and account {receiver} attempts to receive {receive_amt} CBDC...");
    let mut rng = rand::thread_rng();

    let mut c_product_vert = Integer::from(1);

    for txn in &mut *txns {
        c_product_vert *= Integer::from_str_radix(&txn.account_data.get(&sender).unwrap().commitment_value, 10).unwrap();
    }

    if sender == receiver {
        panic!("Transfer of funds unsupported");
    }

    if send_amt <= funds[sender as usize] {
        assert_eq!(verify_commitment(c_product_vert % p.clone(), g.clone(), h.clone(), Integer::from(funds[sender as usize]), sums_blinding[sender as usize].clone(), p.clone()), true, "Proof of assets failed");
        println!("Proof of assets verified.");

    } else {
        panic!("Insufficient funds");
    }

    let (c_send, b_send) = commit_value(Integer::from(0) - Integer::from(send_amt), g.clone(), h.clone(), p.clone());
    let (c_receive, b_receive) = commit_value(Integer::from(receive_amt), g.clone(), h.clone(), p.clone());

    funds[sender as usize] -= send_amt;
    funds[receiver as usize] += receive_amt;

    sums_blinding[sender as usize] += b_send.clone();
    sums_blinding[receiver as usize] += b_receive.clone();

    let mut default_values: Vec<Txn> = Vec::new();
    let mut account_data: HashMap<u64, Txn> = HashMap::new();

    let mut b_summation = Integer::from(0);

    account_data.insert(sender, Txn { commitment_value: c_send.clone().to_string_radix(10), blinding_factor: hex::encode(keys[sender as usize].1.encrypt(&mut rng, Pkcs1v15Encrypt, b_send.clone().to_string_radix(10).as_bytes()).unwrap()) } );
    account_data.insert(receiver, Txn { commitment_value: c_receive.clone().to_string_radix(10), blinding_factor: hex::encode(keys[receiver as usize].1.encrypt(&mut rng, Pkcs1v15Encrypt, b_receive.clone().to_string_radix(10).as_bytes()).unwrap()) } );

    let mut c_product = c_send * c_receive;

    for _ in 0..(number_of_accounts - 3) {
        let (c_default, b_default) = commit_value(Integer::from(0), g.clone(), h.clone(), p.clone());

        b_summation += b_default.clone();
        c_product *= c_default.clone();

        default_values.push(
            Txn {
                commitment_value: c_default.clone().to_string_radix(10),
                blinding_factor: b_default.clone().to_string_radix(10),
            });
    }

    let b_last = Integer::from(0) - (b_send.clone() + b_receive.clone() + b_summation.clone());
    let c_last = (g.clone().pow_mod(&Integer::from(0), &p).unwrap() * h.clone().pow_mod(&b_last, &p).unwrap()) % p.clone();

    c_product *= c_last.clone();

    let mut chosen_account;

    loop {
        chosen_account = rng.gen_range(0..number_of_accounts);
        if chosen_account != sender && chosen_account != receiver {
            break;
        }
    }

    for account in 0..number_of_accounts {
        if account != sender && account != receiver && account != chosen_account {
            let mut random_number;
            loop {
                random_number = rng.gen_range(0..default_values.len());
                if default_values[random_number].commitment_value != Integer::from(0).to_string_radix(10) {
                    sums_blinding[account as usize] += Integer::from_str_radix(&default_values[random_number].clone().blinding_factor, 10).unwrap();
                    account_data.insert(account, Txn {
                        commitment_value: default_values[random_number].clone().commitment_value,
                        blinding_factor: hex::encode(keys[account as usize].1.encrypt(&mut rng, Pkcs1v15Encrypt, default_values[random_number].clone().blinding_factor.as_bytes()).unwrap()),
                    });
                    default_values[random_number].commitment_value = Integer::from(0).to_string_radix(10);
                    break;
                }
            }
        }
    }

    sums_blinding[chosen_account as usize] += b_last.clone();
    account_data.insert(chosen_account, Txn { commitment_value: c_last.to_string_radix(10), blinding_factor: hex::encode(keys[chosen_account as usize].1.encrypt(&mut rng, Pkcs1v15Encrypt, hex::encode(b_last.clone().to_string_radix(10)).as_bytes()).unwrap()) });

    txns.push(TxnData {
        timestamp,
        account_data,
    });

    assert_eq!(verify_commitment(c_product % p.clone(), g.clone(), h.clone(), Integer::from(0), Integer::from(0), p.clone()), true, "Proof of balance failed");
    println!("Proof of balance verified.");

    println!("\nTransaction succeeded.");

}

fn write_to_csv(txns: Vec<TxnData>, number_of_accounts: u64) -> Result<(), Box<dyn std::error::Error>> {
    let mut writer = Writer::from_path("data.csv")?;
    let mut headers = vec![String::from("timestamp")];
    for account in 0..number_of_accounts {
        headers.push(account.to_string());
    }
    writer.write_record(&headers)?;

    for data in txns {
        let mut row = vec![data.timestamp.to_string()];
        let mut values: Vec<String> = Vec::new();

        for account in 0..number_of_accounts {
            let account_data = data.account_data.get(&account).unwrap();
            let account_data = format!("({}, {})", account_data.commitment_value, account_data.blinding_factor);
            values.push(account_data);
        }

        row.append(&mut values);
        writer.write_record(&row)?;
    }

    writer.flush()?;

    Ok(())
}

#[get("/")]
async fn index() -> HttpResponse {
    let file_path = "data.csv";
    let file = std::fs::File::open(file_path).expect("Failed to open CSV file");
    let mut reader = ReaderBuilder::new()
        .has_headers(true)
        .from_reader(file);

    let headers = reader.headers().unwrap().iter().map(|header| header.to_string()).collect::<Vec<String>>();

    let mut rows = Vec::new();
    for result in reader.records() {
        match result {
            Ok(record) => {
                let values: Vec<String> = record.iter().map(|field| field.to_string()).collect();
                rows.push(values);
            }
            Err(err) => eprintln!("Error reading CSV record: {}", err),
        }
    }

    let json = json!({
        "headers": headers,
        "rows": rows,
    });

    HttpResponse::Ok()
        .content_type("text/html; charset=utf-8")
        .body(format!(
            r#"
            <html>
                <head>
                    <style>
                        table {{
                            border-collapse: collapse;
                        }}
                        th, td {{
                            border: 1px solid black;
                            padding: 8px;
                            text-align: left;
                        }}
                    </style>
                </head>
                <body>
                    <h1>Pedersen-committed financial data</h1>
                    <table>
                        {}
                    </table>
                </body>
            </html>
            "#,
            generate_table(json)
        ))
}

fn generate_table(json: serde_json::Value) -> String {
    let mut table = String::new();
    let headers = json["headers"].as_array().unwrap();
    let rows = json["rows"].as_array().unwrap();

    table.push_str("<tr>");
    for header in headers {
        table.push_str(&format!("<th>{}</th>", header));
    }
    table.push_str("</tr>");

    for row in rows {
        table.push_str("<tr>");
        for col in row.as_array().unwrap() {
            table.push_str(&format!("<td>{}</td>", col));
        }
        table.push_str("</tr>");
    }

    table
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut rng = rand::thread_rng();
    let bits = 2048;

    println!("\n------Simulation of a Pedersen commitment-based CBDC system-----\n");

    let (g, h, p) = generate_values();

    println!("\nGenerated g: {}, h: {}, p: {}\n", g.clone(), h.clone(), p.clone());

    let mut keys = Vec::new();
    let mut funds = Vec::new();
    let mut account_data = HashMap::new();
    let mut txns: Vec<TxnData> = Vec::new();

    print!("\nHow many accounts should participate in this simulation? ");
    io::stdout().flush()?;
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let number_of_accounts: u64 = input.trim().parse().unwrap();
    let mut sums_blinding = vec![Integer::from(0); number_of_accounts as usize];
    print!("\nWhat should be the seed funding issued to these accounts? ");
    io::stdout().flush()?;
    let mut input = String::new();
    io::stdin().read_line(&mut input).unwrap();
    let seed: u64 = input.trim().parse().unwrap();

    println!("\nGenerating keypairs...\n");

    for account in 0..number_of_accounts {
        let priv_key = RsaPrivateKey::new(&mut rng, bits)?;
        let pub_key = RsaPublicKey::from(&priv_key);
        keys.push((priv_key, pub_key));
        funds.push(seed);
        let (c, r) = commit_value(Integer::from(seed), g.clone(), h.clone(), p.clone());
        account_data.insert(account as u64, Txn { 
            commitment_value: c.clone().to_string_radix(10), 
            blinding_factor: hex::encode(keys[account as usize].1.encrypt(&mut rng, Pkcs1v15Encrypt, r.clone().to_string_radix(10).as_bytes()).unwrap()) 
        });
        sums_blinding[account as usize] += r.clone();
    }

    txns.push( TxnData {
        timestamp: Integer::from(0),
        account_data,
    });

    loop {
        print!("\n[T]ransact / [A]udit / [E]xit? [t/a/e] ");
        io::stdout().flush()?;
        let mut input = String::new();
        io::stdin().read_line(&mut input).unwrap();
        match input.trim() {
            "T" | "t" => {
                print!("\nSend from which account? [0-{number_of_accounts}] ");
                io::stdout().flush()?;
                let mut input = String::new();
                io::stdin().read_line(&mut input).unwrap();
                let sender: u64 = input.trim().parse().unwrap();
                print!("\nWhat amount to be sent in CBDC? ");
                io::stdout().flush()?;
                let mut input = String::new();
                io::stdin().read_line(&mut input).unwrap();
                let send_amt: u64 = input.trim().parse().unwrap();
                print!("\nReceive by? [0-{number_of_accounts}] ");
                io::stdout().flush()?;
                let mut input = String::new();
                io::stdin().read_line(&mut input).unwrap();
                let receiver: u64 = input.trim().parse().unwrap();
                print!("\nWhat amount to be received in CBDC? ");
                io::stdout().flush()?;
                let mut input = String::new();
                io::stdin().read_line(&mut input).unwrap();
                let receive_amt: u64 = input.trim().parse().unwrap();
                let duration_since_epoch = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap();
                let timestamp = duration_since_epoch.as_nanos();
                transact(Integer::from(timestamp), sender, send_amt, receiver, receive_amt, g.clone(), h.clone(), p.clone(), keys.clone(), number_of_accounts, &mut funds, &mut sums_blinding, &mut txns);
                for txn in &txns {
                    println!("\nTimestamp: {}", txn.timestamp);
                    for account in 0..number_of_accounts {
                        println!("\nAccount {account}: \n Commitment value: {} \n Blinding factor: {}", txn.account_data.get(&account as &u64).unwrap().commitment_value, txn.account_data.get(&account as &u64).unwrap().blinding_factor)
                    }
                }
            }
            "A" | "a" => {
                print!("\nAudit which account? [0-{number_of_accounts}] ");
                io::stdout().flush()?;
                let mut input = String::new();
                io::stdin().read_line(&mut input).unwrap();
                let auditee: u64 = input.trim().parse().unwrap();
                let mut c_product_vert = Integer::from(1);
                for txn in &mut txns {
                    c_product_vert *= Integer::from_str_radix(&txn.account_data.get(&auditee).unwrap().commitment_value, 10).unwrap();
                }
                assert_eq!(verify_commitment(c_product_vert % p.clone(), g.clone(), h.clone(), Integer::from(funds[auditee as usize]), sums_blinding[auditee as usize].clone(), p.clone()), true, "Audit failed");
                println!("\nAudited. Account {auditee} has {} CBDC remaining.", funds[auditee as usize]);
            }
            "E" | "e" => {
                break;
            }
            _ => {},
        }
    }

    write_to_csv(txns.clone(), number_of_accounts)?;

    println!("\nWriting to data.csv...");
    println!("\nStarting server on localhost:8000 for pretty-printing data.csv, press Ctrl-C (SIGINT) after you finish viewing to upload encrypted financial data to IPFS...");

    HttpServer::new(|| App::new().service(index))
        .bind("127.0.0.1:8000")?
        .run()
        .await?;

    println!("\nDemonstrating upload to IPFS..");

    let (cid, password) =  add_file().await?;

    println!("\nSuccessfully encrypted, compressed and uploaded data.csv to IPFS...");
    println!("\nURL: https://{}.ipfs.w3s.link/data.csv", cid);
    println!("\nGenerated password (store safely): {}", password);

    println!("\nDemonstrating IPFS retrieval...");
    retrieve_file(cid, password).await?;

    Ok(())
}
