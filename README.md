# Verifying Fault-Tolerance of Quantum Error Correction Codes

## Prerequisite

* `docker` is required to perform artifact evaluation.
* x86 or amd64 CPU.

## Build

1. Build and run the corresponding Docker image. It will handle all dependencies and packages:

```bash
docker build -t vftqecc .
docker run -it vftqecc
```

2. Inside Docker, you will be at the project directory `/workspace/QuantumSE.jl`. Install the necessary Julia packages by using the following script.

```bash
julia instantiate.jl
```

Then, follow the **Case Study** section to test different examples.

## Case Study 
### Cat State Preparation

The following steps produce the verification results of cat state preparation shown in Fig. 5 in the paper.

Run `example/CatPreparation.jl` with one parameter. The parameter is the number of faults to be tolerated, taking value in $[1, 2, 3, \ldots]$. After the run is completed, the last two lines of output are the verification result ("Pass" or "Fail") and the running time. For example:

When the number of faults is no more than $2$, it is fault-tolerant. For example, if you run:
```bash
julia example/CatPreparation.jl 2
```
then the results should be like
```
>>> Pass!
Cat State Preparation, num_faults=2, time=2.1842598915100098
```

When the number of faults is larger than $2$, it is non-fault-tolerant. For example, if you run:
```bash
julia example/CatPreparation.jl 3
```
then the results should be like
```
>>> Fail!
Cat State Preparation, num_faults=3, time=2.1932621002197266
```

### Fault Tolerance Verification

The results of fault tolerance verification (see Table 1 in the paper) are produced by the following steps.

Run `example/ColorCode.jl`, `example/RotatedSurfaceCode.jl`, or `example/ToricCode.jl` with two parameters. The first parameter is the type of gadget, taking value in [`prep`, `cnot`, `meas`, `ec`]. The second parameter is the code distance, taking values in odd numbers (Color code only supports distances $3$ and $5$). 

Here are some examples:

```bash
julia example/ColorCode.jl ec 5
```

```bash
julia example/RotatedSurfaceCode.jl meas 3
```

```bash
julia example/ToricCode.jl prep 3
```

Then, Run `example/QuantumReedMullerCode.jl` without parameters. 
```
julia example/QuantumReedMullerCode.jl
```

After the run is completed, the last two lines of output are the verification result (should be "Pass") and the running time. For example:
```
>>> Pass!
Color Code, ec, [n,k,d]=[17,1,5], time=20.980690174102783
```

#### Reproducing Table 1
For the reader's convenience, we provide here the parameters corresponding to the results in Table 1.
|  QECC   | [n,k,d] | Prep. | CNOT | Meas. | EC | 
| -------- | ------- | ------ | ------| ------| ------ |
| Color Code  |  [7,1,3] | prep 3 | cnot 3| meas 3 | ec 3|
| Color Code  |  [17,1,5] | prep 5 | cnot 5| meas 5 | ec 5|
| Rotated Surface Code |   [9,1,3] |  prep 3 | cnot 3| meas 3 | ec 3|
| Rotated Surface Code |   [25,1,5] |  prep 5 | cnot 5| meas 5 | ec 5|
| Rotated Surface Code |   [49,1,7] |  prep 7 | cnot 7| meas 7 | ec 7|
| Toric Code | [18,2,3] |  prep 3 | cnot 3| meas 3 | ec 3|
| Toric Code | [50,2,5] |  prep 5 | cnot 5| meas 5 | ec 5|
| Quantum Reed-Muller Code | [15,1,3]  |  N.A. | N.A. | N.A. | no parameter |

The first parameter is the type of gadget to be verified (i.e., Preparation, CNOT, Measurement and Error Correction). The second parameter is the code distance $d$ of the QECC (there is no need to specify $n$ and $k$ since they are determined by $d$). You can set $d$ to any odd number $>1$ (for Color Code, we only support $d\leq 5$). However, larger $d$ may result in significantly longer running times.

You can also use the following script, which can automatically run all experiments in Table 1.
```bash
bash run_table1.sh
```
The experiments are run in row-major order and results are recorded in the file `Table1_results.txt`. Due to the time cost, the row for Rotated Surface Code with $d=7$ is deferred to the end and the time-out setting is skipped.

#### Larger Code Distance
If you set $d$ to a larger value, e.g. run `julia example/RotatedSurfaceCode.jl meas 7`, you may encounter the following error,
```
NERRS should be >= 13
ERROR: LoadError: AssertionError: false
```
Then, you need to provide the required number ($13$ in this case) as the third parameter, that is, run `julia example/RotatedSurfaceCode.jl meas 7 13`.


## Build outside Docker

To use our tool outside Docker, you need to have the following software installed on your system:
* Julia 1.10.5. Due to frequent API changes, we can only support up to Julia 1.10 LTS.
* Bitwuzla SMT solver 0.7.0

More detailed instructions can be found in the file `Dockerfile`.

## Copyright

This project is based on [QuantumSE.jl](https://github.com/njuwfang/QuantumSE.jl),
originally developed by Fang Wang and licensed under the MIT License.

Modifications and extensions © 2025 Kean Chen.
