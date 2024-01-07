# snopt - systematically optimizing sorting network implementations

This repository contains:
- code to generate optimized implementations of arbitrary sorting networks
- code and data from the experiments reported upon in the article

# Installation

Preferably, create a virtual environment using venv or conda. Then install the requirements.
```
pip install -r requirements.txt
```

# Example usage

Generate optimized C implementations for the best known networks from 2 to 16 inputs:
```
python generate.py -v --progress -d generated \
 -f 2 -t 16 \
 -r True \
 --fallback False \
 -b sat \
 --prune True \
 --do-max False \
 --try-min True \
 --try-max False \
 --target C \
 --slice -1 \
 -s jgamble_best
```

Generate optimized asm implementations for networks using Batcher's construction from 2 to 128 inputs:
```
python generate.py -v --progress -d generated \
 -f 2 -t 128 \
 -r True \
 --fallback False \
 -b sat \
 --prune True \
 --do-max False \
 --try-min True \
 --try-max False \
 --target asm \
 --slice -1 \
 -s batcher
```

Generate optimized Python implementations for networks using the Bose-Nelson construction from 2 to 32 inputs:
```
python generate.py -v --progress -d generated \
 -f 2 -t 128 \
 -r True \
 --fallback False \
 -b sat \
 --prune True \
 --do-max False \
 --try-min True \
 --try-max False \
 --target py \
 --slice -1 \
 -s jgamble_bosenelson
```

See the scripts in the `paper` directory for more examples of how to use the code.
