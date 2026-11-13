use regex::bytes::Regex;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

fn caps(re: &Regex, s: &[u8]) -> String {
    match re.captures(s) {
        Some(c) => format!(
            "{},{},{}",
            hex(c.get(1).unwrap().as_bytes()),
            hex(c.get(2).unwrap().as_bytes()),
            hex(c.get(3).unwrap().as_bytes())
        ),
        None => "-".into(),
    }
}

fn main() {
    let m = Regex::new(r"^(?:5.5.5-)?(\d{1,2})\.(\d{1,2})\.(\d{1,3})(?:-\d+)?-MariaDB").unwrap();
    let v = Regex::new(r"^(\d{1,2})\.(\d{1,2})\.(\d{1,3})(.*)").unwrap();
    let mut inputs: Vec<Vec<u8>> = vec![];
    for t in [
        "5.5.5-10.0.17-MariaDB-log", "5.5.5-11.4.7-MariaDB-log", "10.11.2-MariaDB",
        "10.6.25-21-MariaDB-enterprise-log", "5.5.5-10.6.25-21-MariaDB-enterprise-log",
        "8.0.39", "5.7.44-log", "5.6.4-m7-log", "8.0.36-28", "totally-bogus",
        "8.0.32-0ubuntu0.22.04.2",
    ] {
        inputs.push(t.as_bytes().to_vec());
    }
    let small = b"01.-";
    let mut cur: Vec<Vec<u8>> = vec![vec![]];
    for _ in 0..=7 {
        let mut next = vec![];
        for c in &cur {
            inputs.push(c.clone());
            for &x in small {
                let mut d = c.clone();
                d.push(x);
                next.push(d);
            }
        }
        cur = next;
    }
    let alpha = b"0123456789.-5MariaDBx\n";
    let words: [&[u8]; 4] = [b"-MariaDB", b"5.5.5-", b"-", b"."];
    let mut seed: u64 = 0x9E3779B97F4A7C15;
    let mut rnd = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for _ in 0..200000 {
        let len = (rnd() % 31) as usize;
        let mut s = vec![];
        while s.len() < len {
            if rnd() % 5 == 0 {
                s.extend_from_slice(words[(rnd() % 4) as usize]);
            } else {
                s.push(alpha[(rnd() % alpha.len() as u64) as usize]);
            }
        }
        inputs.push(s);
    }
    let toks: [&[u8]; 12] = [b"5.5.5-", b"5x5\n5-", b"1", b"12", b"123", b"1234", b".", b"-", b"-MariaDB", b"-Mari", b"x", b"\n"];
    for _ in 0..200000 {
        let n = (rnd() % 9) as usize;
        let mut s = vec![];
        for _ in 0..n { s.extend_from_slice(toks[(rnd() % 12) as usize]); }
        inputs.push(s);
    }
    let pres: [&[u8]; 4] = [b"", b"5.5.5-", b"5a5\n5-", b"5.5.5"];
    let tails: [&[u8]; 5] = [b"", b"-MariaDB", b"-MariaDB-log", b"-Mari", b"-log"];
    let dig = |r: u64, n: u64| -> Vec<u8> { (0..n).map(|i| b"0123456789"[((r >> (4 * i)) % 10) as usize]).collect() };
    for _ in 0..200000 {
        let mut s = vec![];
        s.extend_from_slice(pres[(rnd() % 4) as usize]);
        s.extend(dig(rnd(), rnd() % 4)); s.push(b'.');
        s.extend(dig(rnd(), rnd() % 4)); s.push(b'.');
        s.extend(dig(rnd(), rnd() % 5));
        if rnd() % 2 == 0 { s.push(b'-'); s.extend(dig(rnd(), rnd() % 3)); }
        s.extend_from_slice(tails[(rnd() % 5) as usize]);
        if rnd() % 4 == 0 && !s.is_empty() { let i = (rnd() % s.len() as u64) as usize; s[i] = alpha[(rnd() % alpha.len() as u64) as usize]; }
        inputs.push(s);
    }
    for s in inputs {
        println!("{}\t{}\t{}", hex(&s), caps(&v, &s), caps(&m, &s));
    }
}
