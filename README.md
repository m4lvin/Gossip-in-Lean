# Gossip in Lean

We use Lean 4 to verify results about Gossip protocols.

- The main result proven in `Gossip.Sufficient` is that $2n-4$ calls are sufficient to make agents experts in a fully-connected graph.

- For the result that $2n-4$ calls are also necessary, a proof sketch has been started in `Gossip.Necessary`.

- In `Evaluation.lean` we provide examples to verify the correctness of the Lean definitions.

Authors:

- Timo Doherty
- Andrei Mărculeşteanu
- Malvin Gattinger

## Code basis

The project was started as part of the following two bachelor theses.

- [Timo Doherty: *Efficient Information Dissemination: Formal Verification of Gossip Protocols Using Lean*](https://scripties.uba.uva.nl/search?id=record_54567) (2024)

- [Tudor Andrei Mărculeşteanu: *Formalization of Necessity Proof for Fully Connected Gossip Problems in Lean*](https://scripties.uba.uva.nl/search?id=record_55963) (2025)

For other references, see also the comments in `Gossip.Necessary`.
