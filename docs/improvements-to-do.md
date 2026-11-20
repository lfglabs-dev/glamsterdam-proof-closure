# Improvements to do

- [ ] **Prove that applying one builder payment preserves every other balance.** The [current theorem](https://github.com/lfglabs-dev/glamsterdam-proof-closure/blob/76f52b975c47f93adbe6eb86585d6193c705c93b/Glamsterdam/Gloas7732/Spec.lean#L324-L344) accounts for the modeled builder debit and the amount queued for withdrawal. Its statement does not track the recipient’s execution-layer balance or other accounts.

  Add a companion theorem over the states before and after applying one covered builder withdrawal. Prove that the paying builder loses exactly the withdrawal amount, the designated recipient gains exactly that amount, and every other builder and execution account keeps its previous balance. Scope the comparison to this withdrawal so unrelated balance changes in the same block are allowed.

- [ ] **Follow a payment through a shared queue.** When a withdrawal is selected for processing, prove it retains the original bid's builder index, fee recipient and amount, including when another queued bid has the same value. Pair this with the balance theorem above.
- [ ] **Check that successive bids stay backed.** Prove that admitting a second bid accounts for the first obligation, including after it moves from pending payment to pending withdrawal.
- [ ] **Check the weight of a whole attester set.** For one payment entry, prove that the increase equals the sum of effective balances of distinct, newly eligible attesters credited to that entry. Cover overlapping attestations and preservation of other entries.
- [ ] **Connect the exit guard to the registry update.** Prove that a request rejected for an outstanding obligation leaves the registry unchanged and that an accepted exit updates only the intended builder's exit fields.
