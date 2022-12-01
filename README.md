# LMC_Martelli-Montanari_unification_algorithm

### Installation
swipl-prolog (`sudo apt install swi-prolog`) : linux<br/>
installer online (Win, MacOS) : http://www.swi-prolog.org/download/stable

### Usage
`swipl main.pl -- [args]`

`?- trace_unif(<P>,<S>)`<br/> pour executer l'algo avec les traces.<br/>
`?- unif(<P>,<S>)`<br/> pour executer l'algo sans trace.<br/><br/>

Pour lancer la procedure de tests : <br/>
`?- consult(tests).` <br/>
`?- run_tests.`
