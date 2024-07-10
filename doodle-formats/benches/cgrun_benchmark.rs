use criterion::{black_box, criterion_group, criterion_main, Criterion};
use doodle::{
    codegen::{generate_code, generate_code_with_hasher},
    FormatModule,
};
use fasthash::FastHasher;
extern crate fasthash;

pub fn codegen_run_benchmark(c: &mut Criterion) {
    let mut module = FormatModule::new();
    let format = doodle_formats::format::main(&mut module).call();
    c.bench_function("cg-run (default hasher)", |b| {
        b.iter(|| black_box(generate_code(&module, &format)))
    });
    c.bench_function("cg-run (farm::Hash64)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::farm::Hash64,
            ))
        })
    });
    c.bench_function("cg-run (farm::Hash128)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::farm::Hash128,
            ))
        })
    });
    c.bench_function("cg-run (lookup::Hash32)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::lookup3::Hash32,
            ))
        })
    });
    c.bench_function("cg-run (mum::Hash64)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::mum::Hash64,
            ))
        })
    });
    c.bench_function("cg-run (murmur::Hash32)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::murmur::Hash32,
            ))
        })
    });
    c.bench_function("cg-run (murmur3::Hash32)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::murmur3::Hash32,
            ))
        })
    });
    c.bench_function("cg-run (sea::Hash64)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::sea::Hash64,
            ))
        })
    });
    c.bench_function("cg-run (spooky::Hash128)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::spooky::Hash128,
            ))
        })
    });
    c.bench_function("cg-run (spooky::Hash64)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::spooky::Hash64,
            ))
        })
    });
    c.bench_function("cg-run (t1ha2::Hash128)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::t1ha2::Hash128AtOnce,
            ))
        })
    });
    c.bench_function("cg-run (t1ha2::Hash64)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::t1ha2::Hash64AtOnce,
            ))
        })
    });
    c.bench_function("cg-run (xx::Hash64)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::xx::Hash64,
            ))
        })
    });
    c.bench_function("cg-run (murmur2::Hash64_x86)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::murmur2::Hash64_x86,
            ))
        })
    });
    c.bench_function("cg-run (murmur3::Hash128_x86)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::murmur3::Hash128_x86,
            ))
        })
    });
    c.bench_function("cg-run (city::Hash64)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::city::Hash64,
            ))
        })
    });
    c.bench_function("cg-run (city::Hash128)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::city::Hash128,
            ))
        })
    });
    c.bench_function("cg-run (metro::Hash128_1)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::metro::Hash128_1,
            ))
        })
    });
    c.bench_function("cg-run (metro::Hash64_1)", |b| {
        b.iter(|| {
            black_box(generate_code_with_hasher(
                &module,
                &format,
                fasthash::metro::Hash64_1,
            ))
        })
    });
}

criterion_group!(benches, codegen_run_benchmark);
criterion_main!(benches);
