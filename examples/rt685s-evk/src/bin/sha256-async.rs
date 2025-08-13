#![no_std]
#![no_main]

use defmt::{info, trace};
use embassy_executor::Spawner;
use embassy_imxrt::hashcrypt::{self, hasher, Hashcrypt};
use embassy_imxrt::{bind_interrupts, peripherals};
use {defmt_rtt as _, embassy_imxrt_examples as _, panic_probe as _};

bind_interrupts!(struct Irqs {
    HASHCRYPT => hashcrypt::InterruptHandler<peripherals::HASHCRYPT>;
});

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_imxrt::init(Default::default());
    let mut hash = [0u8; hasher::HASH_LEN];

    info!("Initializing Hashcrypt");
    let mut hashcrypt = Hashcrypt::new_async(p.HASHCRYPT, Irqs, p.DMA0_CH30);

    info!("Starting hashes");
    // Data that fits into a single block
    info!("Single hash block");
    hashcrypt.new_sha256().hash(b"abc", &mut hash).await;
    defmt::assert_eq!(
        &hash,
        &[
            0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03,
            0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
        ]
    );

    // Data that fits into two blocks
    info!("Two hash blocks");
    hashcrypt
        .new_sha256()
        .hash(
            b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890!@#$%^&*()",
            &mut hash,
        )
        .await;
    defmt::assert_eq!(
        &hash,
        &[
            0xc6, 0x53, 0xd6, 0xb8, 0x3a, 0x21, 0x1a, 0x73, 0xe4, 0xf2, 0x50, 0x1b, 0xdf, 0x30, 0x53, 0x28, 0xaa, 0x8e,
            0x6f, 0x8f, 0xca, 0x46, 0x16, 0xf7, 0x19, 0x3f, 0xd4, 0xda, 0x5a, 0xca, 0xcc, 0x2e
        ]
    );

    // Data that is exactly one block
    info!("One block exactly");
    hashcrypt
        .new_sha256()
        .hash(
            b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890!@",
            &mut hash,
        )
        .await;
    defmt::assert_eq!(
        &hash,
        &[
            0x85, 0x7c, 0xce, 0x23, 0xb6, 0xba, 0x40, 0xd9, 0xa8, 0x33, 0x0d, 0x93, 0x97, 0x98, 0x1d, 0xa5, 0x8f, 0x5a,
            0x8f, 0x41, 0x34, 0x44, 0xc7, 0xa4, 0x1c, 0x42, 0x01, 0xa1, 0x47, 0x76, 0x51, 0xef
        ]
    );

    // Data where the final block needs to be split over two blocks
    info!("Split final block");
    hashcrypt.new_sha256().hash(
        b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890!@abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ12345678",
        &mut hash,
    ).await;
    defmt::assert_eq!(
        &hash,
        &[
            0x1a, 0xdc, 0x94, 0xa1, 0xa4, 0x10, 0x77, 0x4a, 0x59, 0xf8, 0x60, 0xe3, 0x09, 0xf1, 0x1d, 0x62, 0x1d, 0xae,
            0x44, 0x95, 0x1d, 0xcd, 0xfc, 0xd0, 0x89, 0x90, 0xef, 0xe2, 0xb2, 0x4d, 0xac, 0x79
        ]
    );
    trace!("Hashes complete");
}
