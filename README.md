# Gossip in Lean

We use Lean 4 to verify results about Gossip protocols.

## Standard Gossip

- The main result proven in `Gossip.Sufficient` is that $2n-4$ calls are sufficient to make agents experts in a fully-connected graph.

- For the result that $2n-4$ calls are also necessary, a proof sketch has been started in `Gossip.Necessary`.

- In `Evaluation.lean` we provide examples to verify the correctness of the Lean definitions.

## Self-Correcting Gossip

In the subfolder `Gossip/Error` we formalize Self-Correcting Gossip as presented in this article:

- Giorgio Cignarale, Hans van Ditmarsch, Stephan Felber, Malvin Gattinger, Hugo Rincon Galeana, Vaishnavi Sundararajan:
  *Self-Correcting Gossip Protocols*, Preprint, 2026.
  <https://arxiv.org/abs/2605.05801>

In this setting secrets are bit values and there may be at most one transmission error.
Moreover, agents self-correct by rejecting and deleting secret values they know to be wrong.
Knowledge is defined under the assumption of synchrony or a global clock.
The documentation for this part starts in [`Gossip.Error.Basic`](https://m4lvin.github.io/Gossip-in-Lean/docs/Gossip/Error/Basic.html)
and the article mentioned above contains [an appendix](https://arxiv.org/pdf/2605.05801#page=38) briefly explaining the Lean formalization.

## Authors

- Timo Doherty
- Andrei Mărculeşteanu
- Malvin Gattinger

The project was started as part of the following two bachelor theses.

- [Timo Doherty: *Efficient Information Dissemination: Formal Verification of Gossip Protocols Using Lean*](https://scripties.uba.uva.nl/search?id=record_54567) (2024)

- [Tudor Andrei Mărculeşteanu: *Formalization of Necessity Proof for Fully Connected Gossip Problems in Lean*](https://scripties.uba.uva.nl/search?id=record_55963) (2025)

For other references, see also the comments in `Gossip.Necessary`.
