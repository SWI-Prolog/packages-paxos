cmake_minimum_required(VERSION 2.8.12)
project(swipl-paxos)

include("../cmake/PrologPackage.cmake")

swipl_plugin(paxos
	     PL_LIBS paxos.pl)
