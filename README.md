# CCICheck

CCICheck is a methodology and automated tool for verifying that a particular
pipeline, memory hierarchy, and coherence protocol correctly work together to
enforce the architectural consistency model of the ISA implemented by the
microarchitecture. In other words, it conducts microarchitectural consistency
verification in a CCI-aware manner.

### Citing CCICheck

If you use CCICheck in your work, we would appreciate it if you cite our paper:

Yatin A. Manerkar, Daniel Lustig, Michael Pellauer, and Margaret Martonosi. "CCICheck:
  Using µhb Graphs to Verify the Coherence-Consistency Interface",
  *The 48th Annual IEEE/ACM International Symposium on Microarchitecture (MICRO)*,
  Waikiki HI, USA, December 2015.

### Contacting the authors

If you have any comments, questions, or feedback, please contact Yatin Manerkar
at manerkar@princeton.edu, or visit our GitHub page,
github.com/ymanerka/ccicheck.

### Status

Though CCICheck is capable of handling a wide range of microarchitectures, it
is at this point a research tool rather than an industry-strength
verification toolchain. We would appreciate any suggestions or feedback either
in approach or in implementation. If you are interested in any particular
feature, missing item, or implementation detail, please contact the authors and
we will try to help out as best we can.

## Building and Using CCICheck

### Prerequisites

CCICheck is written in Coq and extracted to OCaml for compilation to a native
executable. It has the following prerequisites:

- Coq
  - tested with Coq 8.4pl5 (October 2014)
- OCaml
  - tested with OCaml 4.01.0
- herd, part of diy (http://diy.inria.fr/herd)
  - tested with herd 5.99-D (as part of diy-5.99-D)
- neato, part of GraphViz (only for visualization)
  - tested with 2.36.0 (20140111.2315)

The authors have compiled and executed CCICheck successfully on both Linux and Mac.

## Usage

`ccicheck -i <litmus test> -o <generated neato graph> [-p <processor name>] [-f]`

The use of the `-f` flag enables "fast mode", in which only the first observable graph
(if one exists) is produced as output (pruned graphs and those with unsatisfiable
constraints are discarded). This is sufficient for litmus tests with both allowed
outcomes (as only one execution allowing the outcome need be found) and forbidden
outcomes (as a consistency violation for forbidden outcomes will be detected just
by finding one acyclic graph, and if none is found then the outcome is not
observable on the target microarchitecture, as required).  The use of fast mode
results in noticeably improved runtimes over the case when all graphs are kept track of.

By default, if the `-p` flag is not provided, CCICheck will use the
`FiveStagePrivL1L2_CCL2_Processor`. If the `-p` flag is provided and CCICheck doesn't
recognize the processor name provided to the flag, it will print a list of
processors it does recognize, and then it will exit. To see this list, just provide
any non-existent processor name to `-p`:

`ccicheck -i <litmus test> -o <generated neato graph> [-p asdfg] [-f]`

## Sample Usage

### Running a single litmus test on a processor

0. Add `herd`, etc. to your `PATH`.
1. `mkdir graphs`
2. `./src/ccicheck -i tests/x86tso/mp.litmus -o graphs/mp.gv`
3. `neato -Tpdf graphs/mp.gv -o graphs/mp.pdf`

If you encounter errors when running `neato` with `-Tpdf`, try going to ps first
and then to PDF:

3. `neato -Tps2 graphs/mp.gv -o graphs/mp.ps`
4. `ps2pdf graphs/mp.ps`

### Running a set of litmus tests on a processor

The `runpipe.sh` script allows multiple litmus tests to be run in parallel on a
processor specification, each with a separate instance of CCICheck. For example:

`./runpipe.sh ../tests/x86tso/ alltests FiveStagePeekabooProcessor 8`

will run CCICheck on the tests named in `alltests` that reside in the
`../tests/x86tso/` directory on the `FiveStagePeekabooProcessor` microarchitecture
specification with 8 concurrent instances of CCICheck at a time.

### Running a set of litmus tests on multiple processors

This can be done by using the `runpipes.sh` script, which takes in a list of
processors to run the tests on in addition to the other arguments provided
to `runpipe.sh`. For example:

`./runpipes.sh ../tests/x86tso/ alltests procs 8`

will run CCICheck on the tests named in `alltests` that reside in the
`../tests/x86tso/` directory on the processors listed in `procs`
with 8 concurrent instances of CCICheck at a time.

## Design Approach

CCICheck is written in Coq, a theorem prover/verification assistant.
Coq has been used to rigorously and formally verify mathematical
theorems such as the four color theorem, and it has been used to produce
C compilers which provably produce correct C code. CCICheck itself does not
yet contain any verified theorems or processes. Nevertheless, we chose Coq to
make integration with other formal models written using Coq easier, and to
leave open the possibility of making CCICheck more rigorous in the future.

We are also interested in using CCICheck as a practical tool.
For this reason, we auto-extract our code from Coq to OCaml (using the built-in
Coq methodology for doing so), and we compile this code to run natively.

## Extending CCICheck

### Wish List

Planned future features:

 - A more usable front-end for specifying microarchitectural orderings.
 - Example microarchitectures for Power and ARM, and detailed models of certain
   types of GPUs

Longer-term hopes:

 - Conduct formal analysis of CCICheck using Coq (proving theorems about our analysis, etc.)
 - Integrate CCICheck with other external tools at different levels of the
   programming stack, so that we might e.g., have a complete verifiable
   flow from high-level languages through architecture to microarchitecture.
