# Drafting laws from a clause

A regulated workflow's laws come from text: a clause of HIPAA, GDPR, a state code, a contract. Turning a clause into
a law is a reading, and a reading can be wrong. This note says how gdp-wired splits that work between a drafter
(often a language model) and a person, and what is trusted at each step.

## The workflow

1. **Ask.** `gdp-wired draft <file> --clause-file clause.txt --cite "45 CFR 164.524(b)(2)"` reads the rule from the
   code, as `check` does, and prints the question (core/draft.ts's `draftPrompt`):
   - the clause and its reference;
   - the code's names and their roles;
   - what a law can say.

   Give it to any drafter. `--llm <command>` pipes it to a command and reads the answer from its stdout, for example:

       --llm 'pi --provider openai --model gpt-6.1-terra --no-session -p "$(cat)"'

   `--answer <file>` reads an answer written elsewhere.
2. **Read.** The answer is a JSON array of laws, each with its method, name, expression and the words of the clause
   it answers. Each law is read over the code's names exactly as `check` reads it (`vetDrafts`). A law that names
   something the code doesn't have, or that the law syntax can't read, is refused with the reason before anyone
   reviews it.
3. **Paste.** For each law it keeps, `draft` prints two comments and where they go (the line above a method, or the
   class):

       # gdp: law access within 30 days: requests[rid].fulfilled implies now - requests[rid].received < 30 days
       # gdp: cite access within 30 days: 45 CFR 164.524(b)(2): "no later than 30 days after receipt" [unreviewed: drafted by gpt-6.1-terra]

4. **Check.** `gdp-wired check` proves the law or breaks it with a run, as it does any law. The citation is printed
   with the law, and the summary counts the laws cited unreviewed.
5. **Sign.** A person reads the clause beside the law. If it says what the clause requires, they replace
   `[unreviewed: ...]` with `[reviewed-by: <name>, <date>]`. If it doesn't, they change or delete it.
6. **Gate.** `check --require-review` exits 2 while any law is cited unreviewed, so CI can hold a regulated
   repository to signed laws.

## What is trusted, and by whom

- **The proof.** The verdict is about the law as written, against the code as read. This is the kernel's, checked
  again in Lean, whoever drafted the law.
- **Faithfulness to the clause.** Nothing in gdp-wired checks it. A drafter can:
  - draft a law that is weaker than the clause (proven, and beside the point);
  - read the code's behaviour into the law (proven because it restates the code);
  - miss a part of the clause.

  The question tells the drafter to state what the clause requires, not what the code does. It also tells the
  drafter to leave out what the code doesn't hold. Only a person's review settles either.
- **The sign-off.** `[reviewed-by: ...]` is text in the code, like the citation. It records that a person signed,
  and git records who changed it; gdp-wired doesn't authenticate it. It goes into each certificate's `meta` with
  the citation and, like `meta`, is never read by a checker.
- **The calendar and the restatements.** A deadline in business days is counted over the calendar in gdp.toml. "One
  month" restated as 30 days is the reader's choice. Both are statements a person makes and reviews with the law.

## What it doesn't do

- **No legal advice.** A citation names the public text a law answers. It never says the code complies with that
  text, and a proven law never says so either.
- **No retrieval.** The person supplies the clause's text; nothing fetches regulation text.
- **No inserting.** The comments are printed, not written into the file: where a law goes is part of the review.
