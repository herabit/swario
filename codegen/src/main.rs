use std::{collections::BTreeMap, fs, num::NonZero, process::Command};

use anyhow::Context;
use core::fmt::Write;
use git2::Repository;
use indoc::writedoc;
use scalar::Scalar;
use vector::Vector;

pub mod scalar;
pub mod vector;

pub fn all_vectors() -> anyhow::Result<Vec<Vector>> {
    Scalar::ALL
        .iter()
        .copied()
        .filter(|scalar| scalar.width().is_some())
        .flat_map(|scalar| {
            scalar
                .supported_counts()
                .iter()
                .copied()
                .map(move |lanes| Vector::new(scalar, lanes))
        })
        .collect::<Result<_, _>>()
}

fn main() -> anyhow::Result<()> {
    let vectors = all_vectors().context("creating vector types")?;
    let mut files: BTreeMap<&str, String> = BTreeMap::new();

    println!("Generating the source tree");

    // Generate all of the vector files.
    for vector in &vectors {
        // let file_path = {
        //     let mut path = "src/".to_owned() + vector.scalar.name() + ".rs";

        //     path.leak()
        // };
        //
        let path = &*{ "src/".to_owned() + vector.scalar.name() + ".rs" }.leak();
        let output = files.entry(path).or_default();

        vector
            .write_all(output)
            .with_context(|| format!("generating {path}"))?;
    }

    // Generate the lib.rs
    files.insert("src/lib.rs", {
        let mut out = String::new();

        let scalars = Scalar::ALL.iter().copied().filter_map(|s| {
            if let Some(..128) = s.width().map(NonZero::get) {
                Some(s.name())
            } else {
                None
            }
        });

        for s in scalars {
            writedoc!(
                &mut out,
                "
                    /// Vectors containing [`prim@{s}`] elements.
                    pub mod {s};

                    #[doc(inline)]
                    pub use {s}::*;
                "
            )?;
        }

        out
    });

    // Open the git repo.
    let repo = Repository::open_from_env().context("failed to open git repo")?;
    let workdir = repo.workdir().unwrap();

    println!("Writing the source tree");

    // Write out all the files
    for (path, content) in &files {
        println!("Writing {path}");
        fs::write(workdir.join(path), &content).with_context(|| format!("writing {path}"))?;
    }

    println!("Formatting the code");

    // Format the files.
    // std::env::set_current_dir(workdir).context("changing directory")?;
    Command::new("cargo")
        .args(["fmt", "--all"])
        .status()
        .context("running cargo fmt")?;

    Ok(())
}
