# icon-why3
Why3 plugin for icon project

## Install
Under an opam environment, the commands below will install the plugin for Why3.
```
$ git clone https://github.com/SoftwareFoundationGroupAtKyotoU/icon-why3.git
$ cd icon-why3
$ opam install .
```

## Usage
After installing the plugin, Why3 can read our input file as an extra format like below.
```
$ why3 ide examples/boomerang.tzw
```

To inspect the plugin behavior, you can obtain the intermediate WhyML code as follows.

```
$ icon examples/boomerang.tzw
```

## Case studies
You can find examples under `./examples`.
We could use our `icon_simplify` transformations, which is installed as a part of the plugin, for large goals.
