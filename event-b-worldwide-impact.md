# Event-B is not dead. It is small, specialist, and badly documented.

*A sourced inventory of the people, projects, dates, and open artefacts behind
Event-B.*

**Research checked:** 31 July 2026

There is a reasonable reason to think Event-B is dead. It is not a fashionable
programming language. It is rarely visible in general software-engineering
courses. Industrial users often publish a paper or a certification result, not
their model files. Search results therefore show a small and scattered
community.

But “not mainstream” and “dead” are different claims.

The evidence supports a narrower, more useful conclusion: **Event-B is alive as
a specialist formal-methods ecosystem, with continuing tool development,
teaching activity, research, and industrial use. It is not a mass-market
development method, and its public footprint is much smaller than its actual
industrial footprint.**

That distinction matters. If we want Event-B to grow, the community should stop
expecting industrial confidentiality to look like open-source activity and start
publishing reproducible models, proof statistics, licences, tool versions, and
teaching material.

## The strongest evidence that it is still alive

### 2 July 2026: Rodin 3.10

The official Event-B wiki records the release of **Rodin 3.10 on 2 July 2026**.
Its release notes document an update to Eclipse 4.38 and Java 21, alongside bug
fixes. Rodin is the open-source Eclipse-based IDE for Event-B: it supports
modelling, refinement, proof-obligation generation, theorem proving, model
checking, and simulation. [Rodin news and release notes][rodin-news]

### 18 May 2026: the thirteenth Rodin workshop

The official **Rodin User and Developer Workshop 2026** page lists the
thirteenth workshop for **18 May 2026 in Tokyo, with a hybrid format**. The
programme includes timed Event-B constraints, a Rust Event-B toolchain, matrix
theory, Event-B education, and new proof and modelling tools.

The named organisers are **Asieh Salehi Fathabadi** (University of
Southampton), **Laurent Voisin** (Systerel), **Neeraj Kumar Singh**
(INPT-ENSEEIHT/IRIT Toulouse), **Michael Leuschel** (Heinrich Heine
University Düsseldorf), and **Thai Son Hoang** (University of Southampton).
[Workshop page and programme][rodin-workshop-2026]

This is not evidence of mass adoption. It is, however, difficult to reconcile
with the claim that nobody is maintaining or using the method.

### 23 July 2026: a new ProB proof-system paper

**Katharina Engels, Jan Gruteser, and Michael Leuschel** published
“Encoding Event-B Proof Rules in Prolog: An Interactive Sequent Prover for
ProB” on arXiv on **23 July 2026**. The work encodes more than 600 Event-B
proof rules, integrates them with ProB and Rodin, and provides proof-tree
visualisation, Rodin import/export, and an explicit teaching goal: giving
students direct control over proof-rule selection.
[Paper and author record][prob-proof-2026]

That is particularly relevant to the “nobody is teaching it” concern. The
paper does not prove that Event-B is widely taught; it does prove that teaching
and proof engineering remain active concerns in 2026.

### A current textual toolchain: Rossi

**Denis Efremov** is developing **Rossi**, a Rust parser, static checker,
command-line tool, and language server for Event-B. The project supports
plain-text `.eventb` files and round-tripping to Rodin’s native XML formats.
Rossi is released under **MIT OR Apache-2.0** and has packages for several
operating systems. [Rossi project site][rossi]

This is a useful sign of renewal: the community is not restricted to an
Eclipse-only workflow. It is also a reminder that Event-B’s current activity is
often visible in small specialist tools rather than in large commercial
platforms.

## The people and projects that built the ecosystem

### 2004–2007: RODIN

The original EU-funded **RODIN — Rigorous Open Development Environment for
Complex Systems** project ran from **1 September 2004 to 31 August 2007** with
an EU contribution of **€4,397,850**.

The central figures included **Jean-Raymond Abrial**, who created B and
developed Event-B; **Michael Butler**, **Stefan Hallerstede**, **Thai Son
Hoang**, **Farhad Mehta**, and **Laurent Voisin**. Their foundational paper is:

> J.-R. Abrial, M. Butler, S. Hallerstede, T. S. Hoang, F. Mehta, and L.
> Voisin, “Rodin: An Open Toolset for Modelling and Reasoning in Event-B,”
> *International Journal on Software Tools for Technology Transfer*, 2010.

The paper is the formal reference for the toolset, not just a software
announcement. [DOI: 10.1007/s10009-010-0145-y][rodin-paper] The project record
and dates are available from the European Commission’s CORDIS archive.
[CORDIS RODIN project][cordis-rodin]

### 2008–2012: DEPLOY

The EU **DEPLOY** project took Event-B from a research toolset toward
industrial deployment. Its target domains included automotive, aerospace,
railway, enterprise information systems, and microprocessor design. The
project’s industrial lessons were collected in:

> M. Butler, M. Leuschel, S. Mehta, and others, eds., *Industrial Deployment
> of System Engineering Methods*, Springer, 2013.

The book describes how Event-B was introduced to industrial organisations,
including the need for training, support, tools, and realistic modelling
processes. [Springer book record][deploy-book]

### 2011–2013: New York City Transit Line 7 / Flushing CBTC

For the New York City Transit Line 7 modernisation, **Denis Sabatier, Lilian
Burdy, Antoine Requet, and Jérôme Guéry** reported formal proofs for the
communications-based train-control system. The work addressed properties such
as no collision, no derailment over an unlocked switch, and no overspeed. The
formal paper appeared in **ABZ 2012**, although the industrial work is dated
**2011–2013** by CLEARSY.

> D. Sabatier, L. Burdy, A. Requet, and J. Guéry, “Formal Proofs for the NYCT
> Line 7 (Flushing) Modernization Project,” ABZ 2012, LNCS 7316, pp. 369–372.

[DOI: 10.1007/978-3-642-30885-7_34][nyct-paper] · [CLEARSY project record][nyct-clearsy]

Important terminology warning: the peer-reviewed paper calls this the **B
method**, while later CLEARSY material describes the system-level approach as
**Event-B/Atelier B**. Do not present the famous Paris Metro Line 14 work as
Event-B: it is a classical B success story and a predecessor, not an Event-B
model.

### 2011–2013: SafeCap railway capacity and safety

**SafeCap** was an EPSRC/RSSB project involving the University of Newcastle,
Swansea University, and Invensys Rail. The project ran from **February 2011 to
July 2013**, with a Swansea share of **£451,190**. It developed a formal,
proof-oriented approach to railway capacity and safety analysis.

The later paper by **Alexei Iliasov, Dominic Taylor, Linas Laibinis, and
Alexander Romanovsky** reports verification of **26 real-world mainline
interlockings** over a two-year period. It describes SafeCap as an advisory
tool that supplements, rather than replaces, manual checking and testing.
[REF impact case study][safecap-ref] · [2021 paper][safecap-paper]

This is a good example of why visibility is misleading: a serious industrial
deployment can produce a case study and a paper without producing a public
GitHub repository containing the customer’s railway models.

### 2017–2021: Paris OCTYS CBTC

The OCTYS work involved **Mathieu Comptier, David Déharbe, Julien Molinero
Perez, Louis Mussat, Pierre Thibaut, and Denis Sabatier**. Their paper,
published in **2017**, presents a rigorous Event-B safety analysis of a CBTC
system used in the Paris transport context. CLEARSY’s project page was
published on **25 May 2021** and describes the target properties as SIL4-level
safety concerns including collision and derailment avoidance.

> M. Comptier, D. Déharbe, J. Molinero Perez, L. Mussat, P. Thibaut, and D.
> Sabatier, “Safety Analysis of a CBTC System: A Rigorous Approach with
> Event-B,” RSSRail 2017, pp. 148–159.

[DOI: 10.1007/978-3-319-68499-4_10][octys-paper] · [CLEARSY OCTYS record][octys-clearsy]

### 2019: Alstom URBALIS CBTC zone controller

**Mathieu Comptier, Michael Leuschel, Luis-Fernando Mejia, Julien Molinero
Perez, and Mareike Mutz** published a property-based Event-B model and
validation approach for an **Alstom URBALIS CBTC zone controller** in
**RSSRail 2019**.

> M. Comptier, M. Leuschel, L.-F. Mejia, J. Molinero Perez, and M. Mutz,
> “Property-Based Modelling and Validation of a CBTC Zone Controller in
> Event-B,” RSSRail 2019, pp. 202–212.

[DOI: 10.1007/978-3-030-18744-6_13][urbalis-paper]

The careful version of the claim is that Event-B was used at the **system
analysis and validation level** around a product whose wider development
history also involves classical B. That is valuable, but it is not the same as
saying that the entire production codebase was generated from Event-B.

### 2018–2020: Hybrid ERTMS/ETCS Level 3 and EULYNX

The ABZ 2018 case study modelled a **hybrid ERTMS/ETCS Level 3** railway
system. **Dana Dghaym, Michael Poppleton, and Colin F. Snook** described a
diagram-led Event-B development using iUML-B. The case study reached nine
refinement levels and was connected to industrial railway concerns involving
DB Netz and EULYNX.

> D. Dghaym, M. Poppleton, and C. F. Snook, “Diagram-Led Formal Modelling
> Using iUML-B for Hybrid ERTMS Level 3,” ABZ 2018.

[ABZ publication record][ertms-paper] · [University of Southampton UML-B
industrial page][uml-b-industrial]

The public record is unusually explicit about the boundary: a ProB/Rodin
publication says that the code implementing the HL3 case study was
**confidential**. The paper and public descriptions are available; the complete
industrial implementation is not. [ProB integration paper][prob-api-paper]

### 2010s: spacecraft, processors, and enterprise software

Event-B was not only a railway method.

* **BepiColombo:** Space Systems Finland used Event-B in the DEPLOY period for
  the spacecraft’s data-processing and control-related developments, including
  the MIXS/SIXS instruments and SpaceWire-related components. The public
  record is a technical paper and project report, not a released ESA flight
  model. [BepiColombo/Event-B report][bepicolombo-paper]

* **XMOS XCore:** **Stephen Wright and Kerstin Eder** reported the industrial
  deployment of Event-B in **2013** for the formal modelling of the XCore
  microprocessor instruction set. [Formal reference][xcore-paper] · [public
  project report][xcore-report]

* **Japan DSF:** The National Institute of Informatics worked with **NTT
  Data, Fujitsu, NEC, Hitachi, Toshiba, and CSK** on the Distributed Software
  Factory collaboration. Event-B was used in feasibility studies for
  business-critical enterprise software. [NII project record][dsf-nii] · [NTT
  Data announcement][dsf-ntt]

* **ARINC 653:** **Yongwang Zhao, Zhibin Yang, David Sanan, and Yang Liu**
  published a complete Event-B formalisation of the safety-critical operating
  system standard in **2015** and reported six hidden errors. A 2023 paper by
  **Feng Zhang, Leping Zhang, Yongwang Zhao, Yang Liu, and Jun Sun** extended
  the work to the multi-core version with seven refinement layers.
  [2015 paper][arinc-paper] · [2023 paper record][arinc-multicore]

* **ErbB signalling biology:** **Usman Sanwal, Thai Son Hoang, Luigia Petre,
  and Ion Petre** published a large Event-B model of the ErbB signalling
  pathway in **2022**. The model represented 1,320 reactions as 242 events,
  with all reported proof obligations discharged automatically. This is a
  striking example of Event-B outside embedded and railway engineering.
  [Nature paper][erbb-paper] · [open preprint][erbb-preprint]

## Is any of it open source?

**Yes, but mostly the toolchain and selected teaching/research artefacts—not
the complete industrial safety cases.**

### Clearly open

* **Rodin Platform:** the official Event-B documentation calls Rodin open
  source. [Official documentation][rodin-main]
* **UML-B and the Southampton plugins:** the UML-B download page explicitly
  says that UML-B, Event-B, and Rodin are open source. Bundled releases are
  published through the [Rodin-Bundles GitHub repository][rodin-bundles].
* **ProB:** the ProB documentation publishes source locations for its kernel,
  parsers, Java API, JavaFX UI, and Rodin plugin. [ProB developer manual][prob-dev]
* **Rossi:** MIT OR Apache-2.0, with source on GitHub. [Rossi source][rossi-github]
* **Public ProB case studies:** the ProB Java API paper links public code for
  an executable specification example, Event-B Pac-Man, a B chess example,
  and the ProB logic calculator. [Public case-study list][prob-api-paper]
* **Teaching models:** the C11/Event-B teaching page links downloadable
  Event-B models for message passing and Peterson’s algorithm. [Teaching
  artefacts][c11-eventb]

### Publicly described, but not verified as open-source model releases

For NYCT, SafeCap, OCTYS, URBALIS, BepiColombo, XMOS, DSF, ARINC 653, and
ErbB, I found papers, institutional reports, or project descriptions. I did
**not** find a clearly licensed repository containing the complete industrial
model and proof development for each one. That is the honest status to put in a
blog.

For the Hybrid ERTMS/ETCS Level 3 case, the evidence is stronger: the public
ProB paper explicitly says that the implementation code was confidential. The
right wording is therefore “public research account, confidential industrial
artefact,” not “open-source case study.”

## Where `eventb-lean` fits

The project in this repository is not another industrial Event-B model. It is an
independent Lean 4 implementation of the analysis layer around Event-B. Its
position is complementary:

| Existing project | Main role | What `eventb-lean` adds or changes |
| --- | --- | --- |
| Rodin | Established Eclipse IDE, model editor, POG, proof management, and plugins | Reads Rodin files but does not run Rodin. Reimplements the reader, formula parser, type checker, and POG in Lean. |
| ProB | Animation, model checking, constraint solving, and execution | Does not try to replace model checking. It focuses on typed obligations, refinement semantics, and proof provenance. |
| UML-B | Graphical UML-to-Event-B modelling | Provides no graphical editor. Its native front end is Lean, with Rodin XML compatibility. |
| Rossi | Modern text parser, checker, CLI, and language server | Overlaps in text-first tooling. The distinctive target here is a Lean-kernel route for semantics and an auditable trust ledger. |
| Industrial Event-B models | Domain-specific safety, control, biological, or enterprise developments | Uses real Rodin models as a differential corpus; it is not itself a certified railway, spacecraft, or medical system. |

The honest maturity statement is important. In this checkout:

* the reader covers **38/38** corpus source files;
* formula parsing covers **1,102/1,102** formula strings;
* type assertions match **940/940** measured cases;
* obligation-name reproduction is **1,105/1,133**;
* derived statement and hypothesis support is still partial; and
* the trust-ledger data structure exists, but complete proof-backend and evidence
  integration remains future work.

The Lean semantics already proves invariant and refinement soundness without
axioms, but it is intentionally a shallow embedding at present. Translating every
resolved Event-B formula into theorem-level Lean terms, covering the remaining POG
rules, and attaching actual kernel/SMT/external evidence are still separate work.

So the accurate one-sentence description is:

> **`eventb-lean` is not a replacement for Rodin, ProB, or UML-B; it is a
> Lean-native compatibility, reimplementation, and audit layer that can make
> Event-B’s generated obligations and trust boundaries independently inspectable.**

That is a meaningful open-source contribution because it addresses a weakness the
industrial projects expose: their results are often credible but difficult to
reproduce. A small, pinned corpus and a kernel-checked comparison can turn a paper
claim into an inspectable artefact. It should be presented as an emerging
verification infrastructure project, not yet as a mature replacement toolchain.

## What “production replacement” would require

That phrase is stricter than “can analyse real models.” There are two possible
targets:

* **An independent Event-B analysis backend:** a realistic target for this
  project.
* **A complete replacement for Rodin:** a much larger target involving the IDE,
  plugins, proof management, migration, and long-term release support.

For the first target, I would expect these gates before calling it production
ready:

1. **Compatibility:** P0 through P3b reach full coverage on the current corpus,
   including multi-level refinement chains, all obligation classes, all supported
   assignment forms, well-definedness, guards, simulation, witnesses, goals, and
   hypotheses. The corpus should then grow from two projects to at least ten
   independently sourced projects.
2. **Proof evidence:** P4 must attach replayable evidence to each obligation. A
   Lean proof must be kernel-replayed; an SMT or external result must record its
   solver, version, input digest, and trust mode; an imported Rodin result must
   remain labelled `rodinImported`, never `kernel`.
3. **Semantic translation:** every accepted, resolved formula must either become
   a kernel-facing Lean proposition or produce a precise unsupported-construct
   diagnostic. No accepted syntax may silently turn into an axiom or disappear.
4. **Interoperability:** users must be able to import and export supported Rodin
   models and theories, preserve names and meanings, and receive actionable
   diagnostics for unsupported features. A practical replacement also needs a
   plan for existing Rodin proof trees; the current project explicitly does not
   migrate `.bpr` proofs.
5. **Operational assurance:** reproducible clean builds, stable releases,
   versioned formats, useful diagnostics, performance measurements, documented
   licences, and independent review of the trust boundary.

It does **not** need to reproduce every neighbouring tool. A backend replacement
can deliberately leave graphical UML-B editing to UML-B and counterexample
search to ProB. A whole-workbench replacement would need those capabilities or
well-supported integrations.

The accurate claim today is therefore “Rodin-compatible independent checker and
proof-obligation generator with a Lean semantic foundation.” The stronger claim
“production Event-B analysis backend” becomes reasonable after complete POG and
statement coverage, replayable P4 evidence, wider corpus validation, and a clear
interoperability story.

## What this says about teaching

The teaching situation is weak, but not empty.

Abrial’s **2010** textbook, *Modeling in Event-B: System and Software
Engineering*, was designed as an introductory or advanced formal-methods text
and includes examples, exercises, and projects proved with Rodin.
[Cambridge book record][abrial-book]

The 2026 ProB proof-rules paper explicitly frames interactive proof selection as
a teaching benefit. Rodin’s documentation continues to provide tutorials and
examples. The problem is distribution: Event-B is often taught as an elective,
specialist formal-methods topic, not as part of the standard software curriculum.

So the blog should make a sharper criticism than “nobody teaches it”:

> Event-B has teaching material and active teachers, but it has failed to make
> its teaching ecosystem visible, current, and easy to reproduce for newcomers.

That is a fixable community problem.

## What not to claim

1. **Do not call every B success Event-B.** Paris Metro Line 14 is a classical
   B project. It belongs in the history, but it should be labelled correctly.
2. **Do not claim that a formal model proves the whole deployed system.** A
   proof establishes properties of a model under its assumptions. The
   assumptions, refinement links, code relation, trusted tools, and external
   evidence must be reported.
3. **Do not equate a paper with an open-source release.** A published model
   description is not a repository, and a downloadable PDF is not a licence.
4. **Do not oversell the current community.** Event-B is active, but it is
   specialist, geographically concentrated, and much less visible than TLA+,
   Alloy, Coq, Lean, or mainstream model-checking tools.

## The case for attention

The most credible headline is not “Event-B dominates industry.” It does not.
The credible headline is:

> **Event-B has a remarkable record in high-assurance modelling, but its
> public ecosystem is too quiet, too fragmented, and too hard to reproduce.**

The next phase should focus on four practical commitments:

1. publish complete small models under explicit licences;
2. preserve proof-obligation counts, solver versions, and trust boundaries;
3. maintain a dated registry of teaching courses, industrial users, and public
   case studies; and
4. provide modern, scriptable workflows alongside Rodin’s Eclipse interface.

The method does not need a marketing miracle. It needs an inspectable public
record. That is how a specialist formal method becomes visible again.

## Formal references and source links

The links below are either official project pages, institutional repositories,
publisher/DOI records, or the authors’ open preprints. They were checked for
the dates, names, and claims used above on 31 July 2026.

[rodin-news]: https://wiki.event-b.org/index.php/Rodin_Platform_3.10_Release_Notes
[rodin-workshop-2026]: https://wiki.event-b.org/index.php/Rodin_Workshop_2026
[prob-proof-2026]: https://arxiv.org/abs/2607.21191
[rossi]: https://eventb-rossi.org/
[rossi-github]: https://github.com/eventb-rossi/rossi
[rodin-main]: https://wiki.event-b.org/index.php/Main_Page
[rodin-paper]: https://doi.org/10.1007/s10009-010-0145-y
[cordis-rodin]: https://cordis.europa.eu/project/id/511599
[deploy-book]: https://link.springer.com/book/10.1007/978-3-642-33170-1
[nyct-paper]: https://doi.org/10.1007/978-3-642-30885-7_34
[nyct-clearsy]: https://www.clearsy.com/en/references/new-york-city-transit/
[safecap-ref]: https://impact.ref.ac.uk/casestudies/CaseStudy.aspx?Id=5798
[safecap-paper]: https://arxiv.org/abs/2108.10091
[octys-paper]: https://doi.org/10.1007/978-3-319-68499-4_10
[octys-clearsy]: https://www.clearsy.com/en/railway/the-cbtc-octys-safety-analysed-by-clearsy-through-formal-methods/
[urbalis-paper]: https://doi.org/10.1007/978-3-030-18744-6_13
[ertms-paper]: https://abz-conf.org/publication/dghaym2018abz/
[uml-b-industrial]: https://www.uml-b.org/
[prob-api-paper]: https://link.springer.com/article/10.1007/s10703-020-00351-3
[bepicolombo-paper]: https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/172/1/Modules_paper-submitted.pdf
[xcore-paper]: https://doi.org/10.1007/978-3-642-33170-1_9
[xcore-report]: https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/346/1/XCore%20Deploy%20Covering%20Document.pdf
[dsf-nii]: https://research.nii.ac.jp/~nkjm/en/projects.html
[dsf-ntt]: https://www.nttdata.com/global/ja/news/release/2010/112400/
[arinc-paper]: https://arxiv.org/abs/1508.06479
[arinc-multicore]: https://ink.library.smu.edu.sg/sis_research/8480
[erbb-paper]: https://www.nature.com/articles/s41598-022-05308-6
[erbb-preprint]: https://arxiv.org/abs/2105.10344
[rodin-bundles]: https://github.com/eventB-Soton/Rodin-Bundles
[prob-dev]: https://prob.hhu.de/w/index.php?title=Developer_Manual
[c11-eventb]: https://dalvandi.github.io/FTfJP2019/
[abrial-book]: https://doi.org/10.1017/CBO9781139195881
