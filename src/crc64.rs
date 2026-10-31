//! CRC-64/XZ (the ECMA-182 polynomial, reflected, with all-ones init and
//! xorout), which is what Go's `crc64.Checksum` with `crc64.ECMA` computes.

const POLY: u64 = 0xC96C_5795_D787_0F42;

const TABLE: [u64; 256] = {
    let mut table = [0u64; 256];
    let mut i = 0;
    while i < 256 {
        let mut crc = i as u64;
        let mut bit = 0;
        while bit < 8 {
            crc = if crc & 1 == 1 { (crc >> 1) ^ POLY } else { crc >> 1 };
            bit += 1;
        }
        table[i] = crc;
        i += 1;
    }
    table
};

pub fn checksum(data: &[u8]) -> u64 {
    let mut crc = !0u64;
    for &byte in data {
        crc = TABLE[((crc ^ byte as u64) & 0xff) as usize] ^ (crc >> 8);
    }
    !crc
}

#[cfg(test)]
mod tests {
    #[test]
    fn check_value() {
        assert_eq!(super::checksum(b"123456789"), 0x995D_C9BB_DF19_39FA);
    }
}
