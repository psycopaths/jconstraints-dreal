# jConstraints-dReal #
This adds support for the dReal constraint solver in jConstraints. Please consult the [dReal](https://dreal.github.io/) website for more information.

**NOTE** This plugin is at the moment very experimental with some features being incomplete.

## Installation ##
First, get dReal from [dReal website](https://dreal.github.io/). Then:

* Go to the *jConstraints-dreal* folder and run ``` mvn install ```. It should run a lot of test cases - hopefully everything works.
* If the compilation was successful, the jConstraints-dreal library can be found in the JAR file target/jConstraints-dreal[VERSION].jar
* jConstraints loads extensions automatically from the ~/.jconstraints/extensions folder in a users home directory. Create this directory and copy jConstraints-dreal-[version].jar into this folder.

## Usage and Configuration ##
To use dreal, simply put the following in your .jpf file.

```txt
symbolic.dp=dreal
dreal.path=/path/to/dReal/executable
```

More options will be added soon.

## Known Issues ##
Does NOT return a valuation.

Cannot handle (Coral can):
```txt
(set-logic QF_NRA)
(declare-fun y () Real)
(declare-fun x () Real)
(assert (= y ( cos x)) )
(check-sat)
(exit)
```

or

```txt
(set-logic QF_NRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(assert (= (- ( sin x1) ( cos x2)) 0.0) )
(check-sat)
(exit)
```