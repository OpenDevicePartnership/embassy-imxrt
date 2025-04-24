# Working with cargo vet

## Introduction

`cargo vet` is a tool to help ensure that third-party Rust dependencies have been audited by a trusted entity.
It matches all dependencies against a set of audits conducted by the authors of the project or entities they trust.

## Adding a new dependency
If you're updating a dependency or adding a new one, you need to ensure it's been audited.
Please follow this process to ensure compliance:

### Run `cargo vet`
`cargo vet` checks all dependencies against the list of audits listed in _audits.toml_. If no audit is found, and the dependency is not in the exemptions listed in _config.toml_, the audits from imports listed in _config.toml_ are checked.
If any of the imports have the relevant audit, it's added to _imports.lock_ and considered vetted.

#### If `cargo vet` passes
All dependencies are vetted.

#### If `cargo vet` fails
- Audit the dependencies

> Follow the recommendations of the `cargo vet` command output, either `cargo vet diff` for version update or `cargo vet inspect` for new dependencies

- Add the audits

> Use `cargo vet certify` to record the new audits to _audits.toml_

- Re-run `cargo vet`

> Check the audits are complete and all dependencies are passing

<!-- TODO: Commented out until rust-crate-audits is private 
- Decide where the new audits need to be added

> Ideally, we want all new audits to be shared across ODP repositories to reduce the overhead of multiple audits for the same dependencies. To ensure audits are shared, it's recommended to cut and paste the audits as a separate PR to the _audits.toml_ in [rust-crate-audits](https://github.com/OpenDevicePartnership/rust-crate-audits).
> If due to business reasons, the audits are not to be shared across repositories, submit the audits to the _audits.toml_ in the project respository. -->

### Submit PR with the new audits

Submit updated _audits.toml_ and/or _imports.lock_ to the PR to ensure audits are updated.