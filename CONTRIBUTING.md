# Contributing

Questions, bug reports, independent reproductions and focused pull requests are
welcome. Discuss substantial architecture changes or costly hardware experiments
in an issue before starting.

## Pull requests and review

Fork the repository, work on a branch and open a pull request against `main`.
Describe the problem, the change and the evidence supporting it.

Attilio Castano (`@attilio-castano`) maintains the project. All changes to `main`
go through pull requests, and contributions require his code-owner approval.
Maintainer-authored pull requests use an owner-only review bypass at merge time;
they still go through a pull request. New commits dismiss earlier approvals.

The design explorer workflow validates recordings and source references on pull
requests and publishes the website from `main`. Broader hardware and proof CI
is not configured. Report the local checks you ran, skipped tests and remaining
assumptions. Follow the [validation guide](docs/validation.md) and,
for experiments, the [research workflow](docs/research/README.md). Keep model,
RTL and physical evidence distinct, and preserve historical experiment records.

## License

By intentionally submitting a contribution for inclusion, you agree to license
it under [Apache-2.0](LICENSE). You retain your copyright and must have the right
to contribute the material. Preserve existing third-party attribution and
license notices; see [NOTICE](NOTICE).
