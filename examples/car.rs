extern crate content_archive as car;
extern crate data_encoding;
#[macro_use]
extern crate structopt;

use std::path::PathBuf;
use std::{io, fs};
use std::fs::{File, OpenOptions};

use structopt::StructOpt;

use data_encoding::BASE32_NOPAD;

#[derive(StructOpt)]
#[structopt(name = "car")]
struct Opt {
    /// Length of keys
    key_len: u32,
    #[structopt(parse(from_os_str))]
    /// Location of the content archive to access
    path: PathBuf,
    #[structopt(subcommand)]
    cmd: Command,
}

#[derive(StructOpt)]
enum Command {
    #[structopt(name = "get")]
    /// Read or write a single value
    Get {
        /// Unpadded base 32 key to read
        key: String,
    },
    #[structopt(name = "put")]
    Put {
        /// Unpadded base 32 key to append
        key: String,
    },
    #[structopt(name = "ls")]
    /// List keys
    Ls,
}

fn main() -> io::Result<()> {
    let opt = Opt::from_args();
    
    match opt.cmd {
        Command::Get { key } => {
            let mut key = BASE32_NOPAD.decode(key.as_bytes()).unwrap();
            key.truncate(opt.key_len as usize);
            let data = fs::read(&opt.path)?;
            let reader = car::Reader::new(data).expect("invalid car file");
            if let Some(mut value) = reader.get(&key) {
                let stdout = io::stdout();
                io::copy(&mut value, &mut stdout.lock())?;
            } else {
                eprintln!("not found");
                ::std::process::exit(1);
            }
        }
        Command::Put { key } => {
            let mut key = BASE32_NOPAD.decode(key.as_bytes()).unwrap();
            key.truncate(opt.key_len as usize);
            let mut writer = match OpenOptions::new().read(true).write(true).open(&opt.path) {
                Ok(x) => car::Writer::open(opt.key_len, x)?,
                Err(ref e) if e.kind() == io::ErrorKind::NotFound => car::Writer::new(opt.key_len, File::create(&opt.path)?),
                Err(e) => { return Err(e); }
            };
            let stdin = io::stdin();
            io::copy(&mut stdin.lock(), &mut writer)?;
            writer.finish_value(&key);
            writer.finish()?;
        }
        Command::Ls => {
            let data = fs::read(&opt.path)?;
            let reader = car::Reader::new(data).expect("invalid car file");
            for (key, value) in &reader {
                println!("{} {}", BASE32_NOPAD.encode(key), value.len());
            }
        }
    }
    Ok(())
}
