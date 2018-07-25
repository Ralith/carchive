extern crate carchive;
extern crate data_encoding;
#[macro_use]
extern crate structopt;

use std::path::PathBuf;
use std::{io, fs};
use std::fs::{File, OpenOptions};

use structopt::StructOpt;

use data_encoding::HEXLOWER_PERMISSIVE;

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
        /// Unpadded key to read, in hexadecimal
        key: String,
    },
    #[structopt(name = "put")]
    Put {
        /// Unpadded key to append, in hexadecimal
        key: String,
        /// Extension headers to write, in hexadecimal
        extensions: Option<String>,
    },
    #[structopt(name = "ls")]
    /// List archive contents and value sizes
    Ls,
    #[structopt(name = "ext")]
    /// Print extension header value, in hexadecimal
    Ext {
        length: usize,
    },
}

fn main() -> io::Result<()> {
    let opt = Opt::from_args();
    
    match opt.cmd {
        Command::Get { key } => {
            let mut key = HEXLOWER_PERMISSIVE.decode(key.as_bytes()).unwrap();
            key.truncate(opt.key_len as usize);
            let data = fs::read(&opt.path)?;
            let reader = carchive::Reader::new(data).expect("invalid car file");
            if let Some(mut value) = reader.get(&key) {
                let stdout = io::stdout();
                io::copy(&mut value, &mut stdout.lock())?;
            } else {
                eprintln!("not found");
                ::std::process::exit(1);
            }
        }
        Command::Put { key, extensions } => {
            let mut key = HEXLOWER_PERMISSIVE.decode(key.as_bytes()).unwrap();
            let mut extensions = extensions.map(|x| HEXLOWER_PERMISSIVE.decode(x.as_bytes()).unwrap());
            key.truncate(opt.key_len as usize);
            let mut writer = match OpenOptions::new().read(true).write(true).open(&opt.path) {
                Ok(x) => carchive::Writer::open(x)?.0,
                Err(ref e) if e.kind() == io::ErrorKind::NotFound => carchive::Writer::new(opt.key_len, File::create(&opt.path)?),
                Err(e) => { return Err(e); }
            };
            let stdin = io::stdin();
            io::copy(&mut stdin.lock(), &mut writer)?;
            writer.finish_value(&key);
            writer.finish(extensions.as_ref().map(|x| &x[..]).unwrap_or(&[]))?;
        }
        Command::Ls => {
            let data = fs::read(&opt.path)?;
            let reader = carchive::Reader::new(data).expect("invalid car file");
            for (key, value) in &reader {
                println!("{} {}", HEXLOWER_PERMISSIVE.encode(key), value.len());
            }
        }
        Command::Ext { length } => {
            let data = fs::read(&opt.path)?;
            let reader = carchive::Reader::new(data).expect("invalid car file");
            println!("{}", HEXLOWER_PERMISSIVE.encode(reader.extensions(length).expect("extension length mismatch")));
        }
    }
    Ok(())
}
