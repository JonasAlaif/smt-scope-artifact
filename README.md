# Getting started

Our artifact is provided as a Docker image, which can be run using any recent version of [Docker](https://docs.docker.com/get-docker/). Please start by unzipping the `smt-scope.zip` file to the root of the artifact, such that running `ls smt-scope` from the root of the artifact succeeds.

All commands should be run from the `smt-scope` directory

```bash
cd smt-scope
```

## Using the image

> If any of the commands in this section do not work for you, take a look at [alternatives](#alternatives).

With `docker` installed and in your path, start by loading the `smt-scope` image from the included file. Run the following command

```bash
docker load -i ../smt-scope-arch.tar.gz
```

We provide images for the `arm64` (Apple sillicon Macs) and `amd64` (most other computers) architectures, if you are on a different architecture you will see the following warning:
```
WARNING: The requested image's platform does not match the detected host platform ...
```
In such a case we recommend building the docker image manually for your architecture as described under [alternatives](#alternatives).

### Single file

The image is used to run SMTScope; check that it is working correctly by running the following command

```bash
docker run --rm -it -v ${PWD}/test-smtlib/custom/paper/intro.smt2:/intro.smt2 jonasalaif/smt-scope z3-scope /intro.smt2
```

> On Windows this command must be run in PowerShell, for the `cmd` terminal replace `${PWD}` with `%cd%`.

The expected output is

```text
unknown
Z3 4.8.7
z3-scope error: 
matching loop (17 iters) [ordering]
Error: "errors found"
```

To run SMTScope on an arbitrary smt2 file, replace `${PWD}/test-smtlib/custom/paper/intro.smt2` in the above command with `/path/to/local/file.smt2`.

### Dumping trace file

Aside from single files, we can mount directories to the Docker container. This way, any files created within the container will be saved to the host system. Try running the following command to dump a trace file from SMTScope

```bash
docker run --rm -it -v ${PWD}/test-smtlib:/test-smtlib -e SCOPE_TRACE_FILE=/test-smtlib/intro.log jonasalaif/smt-scope z3-scope /test-smtlib/custom/paper/intro.smt2
```

This should print the same output as before, and additionally create the file `test-smtlib/intro.log` on the host system.

Linux users may run into a permission issue where the Docker container cannot modify files in the mouned directory, this can be fixed by running (and then retrying the above command)

```bash
chmod o+rw -R test-smtlib
```

### Viewing the GUI

SMTScope includes a web-based GUI. To make it available, run the following command

```bash
docker run --rm -it -p 8080:80 jonasalaif/smt-scope python3 -m http.server 80 --directory smt-scope-gui/dist
```

You should now be able to access the GUI by navigating to [`http://localhost:8080`](http://localhost:8080) in your web browser. You can stop the server by pressing `Ctrl+C` in the terminal where the command was run. The server can be run in the background by adding the `-d` flag (i.e., `docker run -d --rm -it -p 8080:80 ...`), but then the docker container will keep running until stopped manually.

Once the GUI is opened in your browser, open the trace file created in the previous step. This can be done either by dragging and dropping the file into the browser window, or by using the "Open trace file" button in the GUI. Next, press the "Matching loops" button in the left sidebar. You should see a view matching Fig. 1 from the paper, save for two small presentational liberties: the `0 = g(0)` oval node, and, on the right, the expression in the bottom turquoise box is rewritten.

## Structure of the artifact

The structure of the artifact is detailed in the [`STRUCTURE.md`](sources/STRUCTURE.md) file.

## Advanced use of the image

We now explain the docker command to run SMTScope in more detail. It can be broken down into

```bash
docker run --rm -it -v ${PWD}/test-smtlib:/test-smtlib -e SCOPE_TRACE_FILE=/test-smtlib/intro.log jonasalaif/smt-scope z3-scope /test-smtlib/custom/paper/intro.smt2
^^^^^^^^^^^^^^^^^^^                                                                            ^^^^^^^^^^^^^^^^^^^^                                               (1)
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^                                                                    (2)
                                                                                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ (3)
```

1. Basic command to run the image.
2. Mounts a file or directory from the host into the container (**mounted directories can be modified from within the container**) and sets an environment variable in the container.
3. The command to run inside the container.

When running the tool, 1. should remain the same, 2. can be used to mount whichever files one wants to work with and 3. selects the command to run. The available commands are `z3-scope` and `smt-scope`. Both can be run without arguments (e.g., without the file path in the command above) to see their usage instructions and available options.

## Alternatives (building locally)

Both images can also be found on Docker Hub (e.g. `docker pull jonasalaif/smt-scope`), additionally the `Dockerfile` to manually build either of the images (e.g. `docker build -t jonasalaif/smt-scope .`) is included in the artifact.

One can also build the tool locally, by following the same steps as in the Dockerfile; the tool depends on `rustc`/`cargo` and `trunk`. Once these are installed run `trunk build --release` from the `smt-scope-gui` directory to build the frontend GUI, and `cargo install --path .` from the `smt-scope-lib` directory will build the commandline executables. Compared to the process described in this file, the artifact can be evaluated locally in exactly the same way, but with just the (3) part of the commands.

# Step-by-Step Instructions

The artifact includes the tools required to verify all of our claims. We describe each in turn, and provide instructions for reproducing the results.

## Section 1

As described in the sections above, the example from Fig. 1 can be found at `test-smtlib/custom/paper/intro.smt2`. It can be viewed in the GUI as described above.

## Section 2

The running example from this section (Fig. 2) can be found at `test-smtlib/custom/paper/running_example.smt2`. The trace file for it can be generated like above, by running

```bash
docker run --rm -it -v ${PWD}/test-smtlib:/test-smtlib -e SCOPE_TRACE_FILE=/test-smtlib/running_example.log jonasalaif/smt-scope z3-scope /test-smtlib/custom/paper/running_example.smt2
```

When the resulting `running_example.log` trace file is opened in the GUI, a similar overview screen to the one in Fig. 3 should be visible. Click on the "Matching loops" button in the left sidebar to view the matching loops. The resulting generalised iteration graph visible on the right should match Fig. 4 from the paper.

To recreate Fig. 6, click on the "Instantiation graph" button in the left sidebar. First click "Disable yield equalities" under Global Operation. Then click "H all but 300 expensive" (under "Graph Operation"), then "Edit", and replace 300 with 62. Lastly, click on the grey oval node at the top left of the graph (labelled "e21"), then click "Selection" in the top bar, and "Hide _". Select the "i14", "e27" and "e31" nodes in the graph by clicking on them while holding `Shift`.

The extended example from Fig. 7 can be found at `test-smtlib/custom/paper/lurking_axiom.smt2`. To print SMTScope's UNSAT extended-core for this file, run the following commands

```bash
docker run --rm -it -v ${PWD}/test-smtlib:/test-smtlib -e SCOPE_TRACE_FILE=/test-smtlib/lurking_axiom.log jonasalaif/smt-scope z3-scope /test-smtlib/custom/paper/lurking_axiom.smt2
docker run --rm -it -v ${PWD}/test-smtlib:/test-smtlib jonasalaif/smt-scope smt-scope ecore /test-smtlib/lurking_axiom.log
```

The expected output of the first command is

```text
unsat
(non_empty-append-ax pre post)
Z3 4.8.7
z3-scope warning: potential multiplicative (3.0x) [non_empty-append]
```

The first two lines are output produced by z3 itself; we can see that the UNSAT core it prints only includes the `non_empty-append` axiom and not the `non_empty-def` axiom. The second command prints the extended core produced by SMTScope, which includes both axioms:

```text
Z3 4.8.7
(non_empty-def-ax pre non_empty-append-ax post)
```

## Section 3

There are two main points to be checked for the evaluation; the results from Table 1, and the various statistics in the text of the section.

### Table 1

#### Generating results

The `.smt2` files we assembled for the evaluation are in the directory `eval/smt-logs/smt2` in the Docker image (we do not include the in the zip file to minimise size). Our entire evaluation can be reproduced by running the following command

> Note: running the evaluation took us 30h, we also provide our result files which can be checked without running the full evaluation (see the next section).

```bash
docker run --rm -it -v ${PWD}/eval/data_other/data:/data -e DATA_DIR=/data jonasalaif/smt-scope /bin/bash ./eval/eval.sh
```

This will run the evaluation and dump a `.data` file for each analysed trace in the `eval/data_other/data` directory. This also runs z3 on each of the smt2 files to generate the trace file before analysing it with SMTScope and the Axiom Profiler. We do this since the trace files themselves are large and it is infeasible to include tens of thousands of them. However, rerunning z3 each time leads to some variations in the results as z3's performance and execution can vary slightly between runs, leading to small differences in the produced traces.

#### Analysing results

We analyse the resulting data in a jupyter notebook. Start the notebook server by running

```bash
docker run --rm -it -p 8888:8888 -v ${PWD}/eval/data_other:/usr/src/artifact/smt-scope/eval/data_other jonasalaif/smt-scope jupyter-lab --allow-root --ip= --no-browser --NotebookApp.token=''
```

Then navigate to [`http://localhost:8888/lab/workspaces/auto-G/tree/eval/Analyse.ipynb`](http://localhost:8888/lab/workspaces/auto-G/tree/eval/Analyse.ipynb) in your web browser. This opened notebook contains our code to process the generated `.data` files and calculate the various results presented in Section 3. Press the "Run all cells" button in the top bar (▶▶, left of the text "Code").

This runs the analysis on the included `final` data files (located in `eval/data_other/final`), which contain the results we used in the paper.
To run the analysis on the data files generated in the previous step, change `version = "final"` line to `version = "data"` in the first code cell, and rerun all cells.

The plot produced by the second code cell should match Fig. 9 from the paper. The line above this stating:

```text
Interest point: 200mb, ap: 40.39561872812122s, ss: 1.0235520682011536s, du: 0.209781995215359s
```

Provides the average times at a trace file size of 200mb (`ap` is Axiom Profiler, `ss` is SMTScope, and `du` is the dummy parser). These should match the numbers presented in the `Q2: Scalability` paragraph of Section 3.

The output of the third code cell should match

```text
Dafny & 13153 & 45 (+6) & 38 (+33) & 43% & 5569812 / 22868098 (24.36%) & 89 / 14881 (0.60%) \\
Silicon & 2724 & 51 (+5) & 37 (+60) & 27% & 1219223 / 5289892 (23.05%) & 114 / 41482 (0.27%) \\
Carbon & 4774 & 17 (+1) & 98 (+194) & 21% & 474660 / 5694677 (8.34%) & 124 / 29501 (0.42%) \\
Fstar & 608 & 8 (+1) & 6 (+6) & 33% & 467494 / 8518848 (5.49%) & 21 / 60185 (0.03%) \\
Verus & 2581 & 3 (+0) & 0 (+5) & 11% & 407 / 647215 (0.06%) & 2 / 12590 (0.02%) \\
Smt-comp & 5465 & 6 (+5) & 32 (+14) & 29% & 4498974 / 4924633 (91.36%) & 32 / 392 (8.16%) \\
Total & 29305 & 130 (+18) & 211 (+312) & 29% & 12230570 / 47943363 (25.51%) & 382 / 159031 (0.24%) \\
```

These numbers should match those presented in Table 1 of the paper (the first 4 columns). There may be small variations due to rerunning z3 as explained above. Looking at the `Total` row, the fifth column (`29%`) lists the execution time of SMTScope as a percentage of the z3's execution time to generate the trace. This should match the `30%` figure presented in the `Q2: Scalability` paragraph in the paper. The last two columns show the number of problematic quantifier instantiations (`12230570`) vs. the total number of quantifier instantiations (`47943363`), and the percentage thereof (`25.51%`), and the number of problematic quantifiers (`382`) vs. the total number of quantifiers (`159031`), and the percentage thereof (`0.24%`). These should match the numbers presented in the last paragraph of the `Q1: Problem Behaviours` subsection.

The output of the fourth code cell should match

```text
Dafny & 13153 & 6 & 7 & 3696 & 821% \\
Silicon & 2724 & 4 & 0 & 772 & 156% \\
Carbon & 4774 & 3 & 1 & 1275 & 393% \\
Fstar & 608 & 0 & 0 & 534 & 273% \\
Verus & 2581 & 1 & 0 & 408 & 354% \\
Smt-comp & 5465 & 3 & 0 & 513 & 729% \\
Total & 29305 & 17 & 8 & 7198 & 634% \\
24.56236137177956
```

This is the data for the Axiom Profiler. The second column lists the number of trace files analysed, the third column is the number of successfully generalised matching loops found, the fourth is the number of unsuccessfully generalised matching loops found, the fifth is the number of trace files for which the tool crashed and the last column lists the execution time in comparison to z3's execution time to generate the trace file (e.g., `821%` means that the Axiom Profiler took 8.21x as long as z3). The total number of matching loops (`17 + 8 = 25`) is lower than the number reported in the paper (`31`) in the third paragraph of the `Q1: Problem Behaviours` subsection. This discrepancy is favourable to the Axiom Profiler in the comparison to our tool, and is because an earlier run of the evaluation had the Axiom Profiler finding more matching loops and those were the ones we manually analysed for false positives.

The last line (`24.56236137177956`) is the percentage of trace files for which the Axiom Profiler crashed. This should match the number presented in the last paragraph of Section 3.

The last text cell in the jupyter notebook lists some of the quantifiers that we manually inspected for the second paragraph of the `Q1: Problem Behaviours` subsection, along with a brief explanation of where the quantifiers come from. Some had the same shape (and thus behaviour) as those already listed, these are noted as `xN` in the description.
