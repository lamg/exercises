# Testing AOT in .Net 8

We have two projects one in C# and one in F#. Both are console
applications that calculate `factorial`.

## Usage

- Install .Net 8
- Run `./compile.sh` once. This will put self contained
  executables in `test_dir`.
- Run `./run.sh` to execute the programs in `test_dir`.
  You can check their sizes with `ls -sh test_dir`.

## Results in my computer

```sh
./run.sh
```

```
factorial(10) = 3628800

real	0m0.008s
user	0m0.006s
sys	0m0.004s
factorial 10 = 3628800

real	0m0.006s
user	0m0.004s
sys	0m0.005s
```

```sh
ls -sh test_dir
```

```
total 5.3M
1.6M cs_aot*
3.8M fs_aot*
```
