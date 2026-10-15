# Target journal: Discrete Mathematics

| Item | Details |
|---|---|
| Journal | Discrete Mathematics |
| Publisher | Elsevier |
| ISSN | 0012-365X (print), confirmed in the Crossref journal record |
| Homepage | https://www.sciencedirect.com/journal/discrete-mathematics |
| Submission | "Submit your article" on the homepage, which opens the journal's Editorial Manager site, https://www.editorialmanager.com/disc/ |
| Template | Elsevier `elsarticle` class (included as `paper/elsarticle.cls`), `preprint,12pt` option, numbered references with `elsarticle-num.bst` |

## Scope fit

Elsevier describes the journal as "a common forum for significant research in
many areas of discrete mathematics and combinatorics", publishing research
articles as Contributions or Notes depending on length. The paper solves a
problem on partitions of the integer interval {1, ..., n} posed by Gurvich and
Naumova (arXiv:2508.00946, math.CO) by an explicit combinatorial construction;
at 10 pages it fits the journal as a short Contribution.

## Length and format

- The manuscript is 10 pages in the `elsarticle` preprint layout (12 pt, single
  column), with four figures.
- Elsevier accepts a first submission as a single PDF; after acceptance the
  LaTeX source, the class file, the `.bib` or `.bbl` file and the figures are
  uploaded. The tex zip and the arXiv tarball in `dist/` contain exactly these
  files.
- Required front matter, all present: title, two authors with addresses,
  emails and ORCIDs (Deep Bhattacharjee is the corresponding author), abstract,
  keywords, MSC 2020 codes (Primary 05A18; Secondary 11B75, 68V15).
- The journal's guide for authors page returned HTTP 403 to the session that
  prepared this file, so any journal-specific page limit or abstract length
  limit was not read; check the guide before submitting.
- The paper ends with Data availability, Competing interests (none) and
  Funding (none) sections; Editorial Manager asks for the same declarations on
  the submission form.

## Policy on AI assistance (Elsevier generative AI policy for journals)

- AI tools may not be listed as authors or cited as authors.
- Use of AI tools in manuscript preparation is disclosed in a separate section
  titled "Declaration of generative AI and AI-assisted technologies in the
  manuscript preparation process", placed before the references; the statement
  appears in the published article. Elsevier's recommended wording is used in
  `paper/main.tex`.
- Use of AI tools in the research process is stated in the declaration and in
  the Data availability section of the paper.
- The authors remain responsible for checking all AI-generated output,
  including references. The references in `paper/refs.bib` were checked against
  the arXiv record of arXiv:2508.00946 and the DOI records of the other two.
- Source: https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals
