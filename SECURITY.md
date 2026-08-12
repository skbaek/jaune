# Security policy

## What this project is, for the purpose of this policy

Jaune is an executable formal specification of the EVM, used as a reference and
as a proof substrate. It is not a client, not a node, and not production
software. It processes fixture files, transition-tool inputs and other data you
supply to it; it holds no keys, opens no network connections, and has no
privileged runtime.

That shapes what a security report against Jaune usefully looks like.

## What to report

**Semantic divergence from Ethereum's consensus rules is the defect class that
matters most here.** If Jaune accepts a block, transaction or execution that
mainnet rules reject, or rejects one they accept, that is the highest-severity
report this project can receive — whether or not it is exploitable in any
conventional sense. It is also the class most likely to matter to somebody
else, because a divergence in a specification is a divergence in everything
derived from it.

Report it publicly as a normal issue. There is no embargo value in a
specification divergence: Jaune runs no infrastructure, and the fastest path to
a correct spec is an open report. Include the input, the fork, and the pins.

Also welcome as ordinary public issues:

- a proof that is weaker than the prose describing it, anywhere in this
  repository or on <https://skbaek.github.io/jaune/>;
- a trust-boundary claim in [`TRUSTED.md`](TRUSTED.md) that does not hold;
- a gate that passes when it should fail.

## What to report privately

Email **seulkeebaek@gmail.com** if you find a conventional software
vulnerability with a plausible victim — for example, an input that causes
`lake exe jaune` to write outside its working directory, execute supplied data,
or exfiltrate the environment it runs in. The fixture and archive handling
paths are the realistic surface; they are exercised by the portability tests
described in the README.

There is no bug bounty. Expect an acknowledgement within about a week.

## What this project does not claim

Nothing here is an audit of any deployed system, and a Jaune theorem is a
statement about Jaune's modeled semantics. [`TRUSTED.md`](TRUSTED.md) states
exactly what a Jaune or Blanc theorem rests on, what is deliberately absent,
and what the theorems do not cover; read it before relying on any result.

## Supported versions

Jaune is developed on `main` against a pinned toolchain and pinned fixture
corpora. There are no long-lived release branches, and no version other than
`main` receives fixes.
