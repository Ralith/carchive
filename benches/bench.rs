#[macro_use]
extern crate criterion;
extern crate carchive as car;
extern crate rand;

use criterion::Criterion;
use rand::{prng::hc128::Hc128Rng, Rng, SeedableRng};

fn make_car<R: Rng>(rng: &mut R, size: usize) -> (Vec<[u8; 25]>, car::Reader<Vec<u8>>) {
    let mut keys = Vec::new();
    let mut buf = Vec::new();
    {
        let mut writer = car::Writer::new(25, &mut buf);
        let mut key = [0; 25];
        for _ in 0..size {
            rng.fill_bytes(&mut key);
            writer.finish_value(&key);
            keys.push(key);
        }
        writer.finish(&[]).unwrap();
    }
    (keys, car::Reader::new(buf).unwrap())
}

fn bench(c: &mut Criterion) {
    c.bench_function_over_inputs(
        "random lookups",
        move |b, &size| {
            let mut rng = Hc128Rng::from_seed(*b"abdfiejsldkairhgabdfiejsldkairhg");
            let (keys, car) = make_car(&mut rng, size);
            b.iter_with_setup(
                || rng.choose(&keys).unwrap(),
                |key| {
                    car.get(key);
                },
            );
        },
        (4..18).map(|x| 2usize.pow(x)),
    );
}

criterion_group!(benches, bench);
criterion_main!(benches);
