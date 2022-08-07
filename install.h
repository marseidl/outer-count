#!/bin/bash


mkdir libs
cd libs
wget https://github.com/lonsing/depqbf/archive/version-6.03.tar.gz
tar xfz version-6.03.tar.gz 
mv depqbf-version-6.03 depqbf
cd depqbf 
./compile.sh 
cd ../..
make
