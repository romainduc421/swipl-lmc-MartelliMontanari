% Definition de l'operateur "?=".
:- op(20,xfy,?=).

% Prédicats d'affichage fournis

% set_echo: ce prédicat active l'affichage par le prédicat echo
set_echo :- assert(echo_on).

% clr_echo: ce prédicat inhibe l'affichage par le prédicat echo
clr_echo :- retractall(echo_on).

% echo(T): si le flag echo_on est positionné, echo(T) affiche le terme T
%          sinon, echo(T) réussit simplement en ne faisant rien.

echo(T) :- echo_on, !, write(T).
echo(_).

:- set_echo.

% Retire les warnings
:- style_check(-singleton).

% +----------------------------------------------------------------------------+
%         ____                         _     _                     __     
%        / __ \                       | |   (_)                   /_ |  _ 
%       | |  | |  _   _    ___   ___  | |_   _    ___    _ __      | | (_)
%       | |  | | | | | |  / _ \ / __| | __| | |  / _ \  | '_ \     | |    
%       | |__| | | |_| | |  __/ \__ \ | |_  | | | (_) | | | | |    | |  _ 
%        \___\_\  \__,_|  \___| |___/  \__| |_|  \___/  |_| |_|    |_| (_)
%                                                                  
% +----------------------------------------------------------------------------+

%%regle(E, R) : Determine la regle de transformation R qui s'applique a l'equation E.
%%----- Def des conditions sur les regles -----%

/*
 * Regle rename : renvoie true si X et T sont des variables.
 * E : equation donnee.
 * R : regle rename.
 * Rename {x ?= t}∪P′;S -> P′[x/t];S[x/t]∪{x=t} si t est une variable
 */
regle(X?=T,rename) :- var(X), var(T), !.
	 
/*
 * Regle simplify : renvoie true si X est une variable et A une
 * constante.
 * E : equation donnee.
 * R : regle simplify.
 * Simplify {x ?= t}∪P′;S -> P′[x/t];S[x/t]∪{x=t} si t est une constante
 */
regle(X?=T,simplify) :- var(X), atomic(T), !.

/*
 * Regle expand : renvoie true si X est une variable, T un terme
 * compose et si X n'est pas dans T.
 * E : equation donnee.
 * R : regle expand.
 * Expand {x ?= t}∪P′;S -> P′[x/t];S[x/t]∪{x=t} si t est composé et x n’apparaît pas dans t
 */	
regle(X?=T,expand) :- var(X), compound(T), \+occur_check(X,T), !.

/*
 * Regle check : renvoie true si X et T sont differents et si X est dans
 * T.
 * E : equation donnee.
 * R : regle check.
 * Check {x?=t}∪P′;S->⊥ si x!=t et x apparaît dans t
 */	
regle(X?=T,check) :- \+X==T, occur_check(X,T), !.

/*
 * Regle orient : renvoie true si T n'est pas une variable et si X en
 * est une.
 * E : equation donnee.
 * R : regle orient.
 * Orient {t?=x}∪P′;S->{x=?t}∪P′;S si t n’est pas une variable
 */
regle(T?=X,orient) :- nonvar(T), var(X), !.

/*
 * Regle decompose : renvoie true si X et T sont des termes composes et
 * s'ils ont le meme nombre d'arguments et le meme nom.
 * E : equation donnee.
 * R : regle decompose.
 * Decompose {f(s,···,s)?=f(t,···,t)}∪P′;S->{s?=t,···,s?=t}∪P′;S
 */	
regle(X?=T,decompose) :- compound(X), compound(T), functor(X,F1,A1), functor(T,F2,A2), F1==F2, A1==A2, !.

/*
 * Regle clash : renvoie true si X et T sont des termes composes (n'ont pas le meme symbole) et
 * s'ils n'ont pas le meme nombre d'arguments.
 * E : equation donnee.
 * R : regle clash.
 * Clash {f(s,···,s)?=g(t,···,t)}∪P′;S->⊥ si f!=g ou m!=n
 */
regle(X?=T,clash) :- compound(X), compound(T), functor(X,N,A), functor(T,M,B), not( ( N==M , A==B ) ), !.

% occur_check(V,T): teste si la variable V apparait dans le terme T
occur_check(V,T) :- var(V), compound(T), arg(_,T,X), compound(X), occur_check(V,X), !;
					var(V), compound(T), arg(_,T,X), V==X, !.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% prédicats de réduction
% reduit(R,E,P,Q) : transforme le système d'équations P en le système d'équations Q par application de la règle de transformation R à l'équation E
% E est représenté par X ?= T.
reduit(rename, X ?= T, P, Q) :-
	elimination(X ?= T, P, Q), 
	!.


reduit(expand, X ?= T, P, Q) :-
	elimination(X ?= T, P,Q), 
	!.


reduit(simplify, X ?= T, P, Q) :-
	elimination(X ?= T, P, Q), 
	!.
	

elimination(X ?= T, P, Q) :-
	X = T,	% Unification avec la nouvelle valeur de X
	Q = P, 	% Q devient le reste du programme
	!.	


reduit(decompose, Fonct1?= Fonct2, P, Q) :-
	functor(Fonct1, _, A),		% recuperer le nombre d'arguments
	decompose(Fonct1, Fonct2, A, Liste), % recuperer les nouvelles eq
	append(Liste,P,Q), % ajout des eq dans le prog P
	!.		
	
decompose(_,_,0,_) :-
	!.
decompose(Fonct1, Fonct2, A, Liste) :-
	% on decremente le no de l'argument parcouru
	New is A - 1,		
	% ajout de l'equation liee au (i-1) -ieme argument
	decompose(Fonct1, Fonct2, New, Res),
	% obtention de l'argument courant pour les deux fct
	arg(A, Fonct1, Arg1),
	arg(A, Fonct2, Arg2),
	% ajout de l'eq arg1 ?= arg2
	append(Res, [Arg1 ?= Arg2], Liste), 
	!.


reduit(orient, T ?= X, P, Q) :-
	% ajout de l'equation inversee dans P
	append([X ?= T], P, Q), !.
	
% facultatifs (systeme dequation est incorrect)
%occurence
reduit(check, _, _, bottom) :- fail.
%gestion de conflits
reduit(clash, _, _, bottom) :- fail.

% Predicat unifie(P)
unifie([]) :- echo("\nUnification terminee."), echo("Resultat: \n\n"),!.
unifie([X|P]) :-
	aff_syst([X|P]),
	regle(X,R),
	aff_regle(R,X),
	reduit(R,X,P,Q), !, unifie(Q).


% +----------------------------------------------------------------------------+
%         ____                         _     _                     ___      
%        / __ \                       | |   (_)                   |__ \   _ 
%       | |  | |  _   _    ___   ___  | |_   _    ___    _ __        ) | (_)
%       | |  | | | | | |  / _ \ / __| | __| | |  / _ \  | '_ \      / /     
%       | |__| | | |_| | |  __/ \__ \ | |_  | | | (_) | | | | |    / /_   _ 
%        \___\_\  \__,_|  \___| |___/  \__| |_|  \___/  |_| |_|   |____| (_)
%		                                                                     
% +----------------------------------------------------------------------------+
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Choix_pondere_1
% Poids des regles
% clash; check > rename; simplify > orient > decompose > expand
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Définition du poids des différentes règles
poids(clash, 7).
poids(check, 7).
poids(rename, 5).
poids(simplify, 5).
poids(orient, 3).
poids(decompose, 2).
poids(expand, 1).

%Effectue l'algorithme d'unification suivant les règles prioritaire définie plus haut
choix_pondere_1(X) :-
	aff_syst(X),
	poids_max(X, R, E),
	extraction(X, E, S),
	aff_regle(R,X),
	reduit(R, E, S, Q),
	choix_pondere_1(Q).
%Lorsque le systeme P est vide, on a terminé l'unification
choix_pondere_1([]) :-
	echo("\nUnification terminee."), echo("Resultat: \n\n"),!.

% Poids max
% Ce predicat compare deux à deux les premieres equations (X et Y) du systeme P et garde celle dont la règle est prioritaire
% L'equation prioritaire est celle dont le poids (W1/W2) est le plus grand.
poids_max([X,Y|P], R, E) :-
        regle(X,R1),
        poids(R1,W1),
        regle(Y,R2),
        poids(R2,W2),
        W1>=W2, %Si X est prioritaire
        !,
	poids_max([X|P], R, E).
poids_max([X,Y|P], R, E) :-
        regle(X,R1),
        poids(R1,W1),
        regle(Y,R2),
        poids(R2,W2),
		W1=<W2, %Si Y est prioritaire
        !,
	poids_max([Y|P], R, E).
%Condition de fin; il ne reste plus qu'un élément
poids_max([X],R,X) :-
	regle(X,R),
	!.



% extraction(P,X,S)
% Permet d'extraire l'equation X du systeme P (sous forme de liste [H|T])
% S est le nouveau systeme sans X
extraction([H|T],X,S) :-
	X == H, %Si la premiere equation (Head) est X 
	S = T, %On l'extrait du systeme R
	!.
%Si la première equation n'est pas X, on teste le reste de la liste (Tail)
extraction([H|T],X,S) :-
	X \== H,
	extraction(T,X,S).
extraction([],_,[]) :- !.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicats pour unifier
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

unifie([X|P],choix_premier):- unifie([X|P]), !.

unifie([X|P],choix_pondere_1) :-
	choix_pondere_1([X|P]), !.

% +----------------------------------------------------------------------------+
%         ____                         _     _                     ____      
%        / __ \                       | |   (_)                   |___ \   _ 
%       | |  | |  _   _    ___   ___  | |_   _    ___    _ __       __) | (_)
%       | |  | | | | | |  / _ \ / __| | __| | |  / _ \  | '_ \     |__ <     
%       | |__| | | |_| | |  __/ \__ \ | |_  | | | (_) | | | | |    ___) |  _ 
%        \___\_\  \__,_|  \___| |___/  \__| |_|  \___/  |_| |_|   |____/  (_)
%		                                                                      
% +----------------------------------------------------------------------------+

%appelle unifie apres avoir desactive les affichages 
unif(P, S) :- clr_echo, unifie(P, S).

%appelle unifie apres avoir active les affichages, affiche "Yes" si on peut unifier "No" sinon (il n'y a donc pas d'echec de la procedure.
trace_unif(P,S) :- set_echo, (unifie(P, S), echo('Yes'), ! ;	
		echo('No') ) .
trace_unif(P, S) :- set_echo, unifie(P,S).


% PREDICATS POUR L AFFICHAGE
aff_syst(W) :- echo('\nsystem: '),echo(W),echo('\n').
aff_regle(R,E) :- echo(R),echo(': '),echo(E),echo('\n\n').

% +----------------------------------------------------------------------------+
% Lancement du programme
:- initialization
        manual.


manual :- write("Unification Martelli-Montanari\n"),
		write("\n\nUtilisez trace_unif(P,S) pour executer l algorithme de Martelli-Montanari avec les traces d execution a chaque etape."),
		write("\nUtilisez unif(P,S) pour executer l algorithme de Martelli-Montanari sans les traces d execution."),
		write("\nP est le systeme a unifier. S represente une strategie a employer: choix_premier, choix_pondere_1, choix_pondere_2."),
		set_echo, !.



