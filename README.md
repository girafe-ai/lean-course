# Formalising Mathematics

This is the course repo for the Lean theorem prover at MIPT. It is a fork of Kevin Buzzard's course "Formalising mathematics" repo taught in Imperial College London.

## Local installation

First you need to install Visual Studio Code and the Lean 4 extension. Instructions for doing that are [here](https://leanprover-community.github.io/get_started.html#regular-install).

Then it's just a matter of installing this repository onto your computer. There are two ways to do this.

### Local installation via point-and-click

The most painless way to install the repository is using VS Code directly. With Lean installed, open any file on your system in VS Code, and then click on the upside-down A

![an upside-down A](png/clone_forall.png?raw=true "an upside-down A")

and select `Open Project` -> `Project: Download Project`. Type in the following URL into the text box which appeared:

```
https://github.com/vasnesterov/formalising-mathematics-mipt-2025
```

and then select the directory where you want the project installed, type in the name of a folder (for example formalising-mathematics-2025) and then wait for a minute or two while everything downloads and compiles. Then accept the suggestion to open the course directory, and you should be up and running. Open up VS Code's file explorer (it looks like this)

![File explorer](png/file_explorer.png?raw=true "File explorer")

and navigate to the `FormalisingMathematics2025` directory, where you should find a whole bunch of directories containing the exercises.

### Local installation via command line

An older way is via the command line. Fire up the same command line which you used to install Lean 4 and type this:

```bash
git clone https://github.com/vasnesterov/formalising-mathematics-mipt-2025
cd formalising-mathematics-mipt-2025
lake exe cache get
```

Now open the folder `formalising-mathematics-mipt-2025` which you just created, using VS Code's "open folder" functionality. You will find all the exercises for the course inside a subdirectory called `FormalisingMathematics2025` (don't confuse these two
directories! One has hyphens, the other does not).
## Online play

If you don't have the 4.5 gigabytes necessary to install all this, or if your computer is too slow to make the experience of using Lean on it fun (you'll need at least 8 gigs of ram, for example, and ideally 16), then you can do the course exercises through a web browser (and you don't need to install anything onto your computer using this method).

### Method 1: via Gitpod.

Just click here: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/ImperialCollegeLondon/formalising-mathematics-2025)

### Method 2: via Codespaces

Just click here: [![Open in Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/ImperialCollegeLondon/formalising-mathematics-2025)

## Course notes

They are [here](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2025/). 
