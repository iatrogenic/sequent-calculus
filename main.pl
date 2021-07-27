/*
    Trabalho Elaborado por:
    ------------------------------------------------
    2099515 - Martim Roberto Alves da Costa,
    2038217 - Jo�o R�ben Moniz Pontes,
    2038017 - Joana Sofia Teixeira Silva,
    2082117 - Rita In�s Bernardino Ribeiro Ramos,
    2038117 - Elvis Miguel Pestana Marques.
*/

/*
Predicados do Prolog utilizados:
write/1: A palavra pr�-definida write � utilizada para escrever; e a
palavra not tem como fun��o negar. writeln/1: Predicado equivalente a
"write(Termo), nl..".
read/1: read(Termo) : � o pr�ximo termo (da linguagem Prolog) inserido
e unifica-o com "Termo".
*/

/*EXERC�CIO 1*/

/*Operadores*/
:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').
:-op(1000, xfy, '==>').

/*membro/2, tal que membro(X,L) � verdadeiro se X � um elemento da lista L.*/
membro(X, [X | _]).
membro(X, [_ | Y]) :- membro(X, Y).

/*elimina/3, tal que elimina(X, L1, L2) � verdadeiro se L2 � uma lista que resulta de remover da lista L1 todos as ocurr�ncias do elemento X.*/
elimina(_, [], []).
elimina(X, [X|Y], Z) :- elimina(X, Y, Z).
elimina(X, [Y|Z], [Y|L]) :- not(X=Y), elimina(X, Z, L).

apl_reg_aut_aux([],[]).
/*As seguintes regras referem-se � nega��o � direita e � esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(neg A, X), elimina(neg A, X, X1), apl_reg_aut_aux([X1 ==> [A|Y]|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(neg A, Y), elimina(neg A, Y, Y1), apl_reg_aut_aux([[A|X] ==> Y1|L], H).
/*As seguintes regras referem-se � conjun��o � direita e � esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A e B, X), elimina(A e B, X, X1), apl_reg_aut_aux([[A,B|X1] ==> Y|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A e B, Y), elimina(A e B, Y, Y1), apl_reg_aut_aux([X ==> [A|Y1], X ==>[B|Y1]|L], H).
/*As seguintes regras referem-se  disjun��o � direita e � esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A ou B, Y), elimina(A ou B, Y, Y1), apl_reg_aut_aux([X ==>[A, B|Y1]|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A ou B, X), elimina(A ou B, X, X1), apl_reg_aut_aux([[A|X1] ==> Y, [B|X1] ==> Y|L], H).
/*As seguintes regras referem-se � implica��o � direita e � esquerda.*/
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A imp B, Y), elimina(A imp B, Y, Y1), apl_reg_aut_aux([[A|X] ==> [B|Y1]|L], H).
apl_reg_aut_aux([X ==> Y|L], H) :- membro(A imp B, X), elimina(A imp B, X, X1), apl_reg_aut_aux([X1 ==> [A|Y], [B|X1] ==> Y|L], H).

apl_reg_aut_aux([X ==> Y|L], [X ==> Y|T]) :- not(membro(neg A, X)), not(membro(neg A, Y)), not(membro(A e B, X)), not(membro(A e B, Y)), not(membro(A ou B, X)), not(membro(A ou B, Y)), not(membro(A imp B, X)), not(membro(A imp B, Y)), apl_reg_aut_aux(L, T).

/*Utilizando as regras do sistema SP acima enunciadas, criou-se um predicado apl_reg_aut/1 cujo o objetivo � aplicar as regras ao sequente.*/
apl_reg_aut(S) :- apl_reg_aut_aux(S, C), write(C).

/*O predicado nao_disjunto/2 verifica se duas listas s�o n�o disjuntas.*/
nao_disjunto(L1, L2) :- membro(X, L1), membro(X, L2).
/*O predicado disjunto/2 verfica se duas listas s�o disjuntas.*/
disjunto(L1, L2) :- not(nao_disjunto(L1, L2)).

/*O predicado axioma/1 verifica se um sequente � axioma.*/
axioma(X ==> Y) :- nao_disjunto(X, Y).

/*O predicado todos_axiomas/1 verifica se de uma lista de sequentes todos s�o axiomas.*/
todos_axiomas([]).
todos_axiomas(X ==> Y) :- axioma(X ==> Y).
todos_axiomas([X ==> Y|R]) :- axioma(X ==> Y), todos_axiomas(R).

/*O predicado ant_t/1 recebe uma lista Ant e retorna a valora��o adequada.*/
ant_t([]).
ant_t(Ant) :- not(is_list(Ant)), write('v(') , write(Ant), write(')=1'), nl.
ant_t([H|T]) :- ant_t(H), ant_t(T).

/*O predicado con_f/1 recebe uma lista Con e retorna a valora��o adequada.*/
con_f([]).
con_f(Con) :- not(is_list(Con)), write('v(') , write(Con), write(')=0'), nl.
con_f([H|T]) :- con_f(H), con_f(T).

/*O predicado v_aux/1 recebe um sequente e aplica os predicados acima definidos.*/
v_aux(X ==> Y) :- list_to_set(X,XS), list_to_set(Y, YS), ant_t(XS), con_f(YS).

/*O predicado valoracao/1 recebe uma lista de sequentes e verifica a sua valora��o.*/
valoracao([]).
valoracao([X ==> Y | _]) :- not(axioma(X==>Y)) , v_aux(X ==> Y).
valoracao([X ==> Y | T]) :- axioma(X==>Y) , valoracao(T).

/*O predicado teorema/1 verifica se o sequente � teorema ou n�o, e se n�o for retorna um exemplo de uma valora��o que o falsifique.*/
teorema(S) :- apl_reg_aut_aux(S, C), todos_axiomas(C), nl, write('Este sequente � um teorema do sistema de sequentes.').
teorema(S) :- apl_reg_aut_aux(S, C), not(todos_axiomas(C)), nl, write('Este sequente n�o � um teorema do sistema de sequentes, e um exemplo de uma valora��o que o falsifique �:'), nl, nl,valoracao(C), nl.

/*EXERC�CIO 2*/

apl_reg_aut_aux_2([],[]).
/*As seguintes regras referem-se � nega��o � direita e � esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(neg A, X), elimina(neg A, X, X1),write('R neg, e --> '), write([X1 ==> [A|Y]|L]), nl,nl, apl_reg_aut_aux_2([X1 ==> [A|Y]|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(neg A, Y), elimina(neg A, Y, Y1), write('R neg, d --> '), write([[A|X] ==> Y1|L]), nl,nl, apl_reg_aut_aux_2([[A|X] ==> Y1|L], H).
/*As seguintes regras referem-se � conjun��o � direita e � esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A e B, X), elimina(A e B, X, X1), write('R e, e --> '), write([[A,B|X1] ==> Y|L]), nl,nl, apl_reg_aut_aux_2([[A,B|X1] ==> Y|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A e B, Y), elimina(A e B, Y, Y1),write('R e, d --> '), write([X ==> [A|Y1], X ==>[B|Y1]|L]), nl,nl, apl_reg_aut_aux_2([X ==> [A|Y1], X ==>[B|Y1]|L], H).
/*As seguintes regras referem-se � disjun��o � direita e � esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A ou B, Y), elimina(A ou B, Y, Y1),write('R ou, d --> '), write([X ==>[A, B|Y1]|L]), nl,nl, apl_reg_aut_aux_2([X ==>[A, B|Y1]|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A ou B, X), elimina(A ou B, X, X1), write('R ou, e --> '), write([[A|X1] ==> Y, [B|X1] ==> Y|L]), nl,nl, apl_reg_aut_aux_2([[A|X1] ==> Y, [B|X1] ==> Y|L], H).
/*As seguintes regras referem-se � implica��o � direita e � esquerda.*/
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A imp B, Y), elimina(A imp B, Y, Y1), write('R imp, d --> '), write([[A|X] ==> [B|Y1]|L]), nl,nl, apl_reg_aut_aux_2([[A|X] ==> [B|Y1]|L], H).
apl_reg_aut_aux_2([X ==> Y|L], H) :- membro(A imp B, X), elimina(A imp B, X, X1), write('R imp, e --> '),write([X1 ==> [A|Y], [B|X1] ==> Y|L]), nl,nl, apl_reg_aut_aux_2([X1 ==> [A|Y], [B|X1] ==> Y|L], H).

apl_reg_aut_aux_2([X ==> Y|L], [X ==> Y|T]) :- not(membro(neg A, X)), not(membro(neg A, Y)), not(membro(A e B, X)), not(membro(A e B, Y)), not(membro(A ou B, X)), not(membro(A ou B, Y)), not(membro(A imp B, X)), not(membro(A imp B, Y)), apl_reg_aut_aux_2(L, T).

/*O predicado apl_reg_aut_2/1 aplica as regras a um sequente e tem como objetivo descrever a constru��o de uma �rvore de dedu��o.*/
apl_reg_aut_2(S) :- nl,apl_reg_aut_aux_2(S, C).


/*EXERC�CIO 3*/


/*Regras do sistema SP nomeadamente, a nega��o, conjun��o, implica��o e disjun��o, tanto � direita como � esquerda que ser�o utilizadas como auxiliares no processo de constru��o de uma �rvore esgotada.*/
rneg_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(neg A, X),
    elimina(neg A, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[X1 ==> [A|Y]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rneg_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(neg A, Y),
    elimina(neg A, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A|X] ==> Y1]], H1, H2),
    elimina([], H2, Novas_Folhas).

re_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A e B, X),
    elimina(A e B, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A,B|X1] ==> Y]], H1, H2),
    elimina([], H2, Novas_Folhas).

re_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A e B, Y),
    elimina(A e B, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[X ==> [A|Y1]], [X ==>[B|Y1]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rimp_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A imp B, Y),
    elimina(A imp B, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A|X] ==> [B|Y1]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rimp_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A imp B, X),
    elimina(A imp B, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[X1 ==> [A|Y]], [[B|X1] ==> Y]], H1, H2),
    elimina([], H2, Novas_Folhas).

rou_d([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A ou B, Y),
    elimina(A ou B, Y, Y1),
    elimina([X ==> Y], Folhas, H1),
    append([[X ==>[A, B|Y1]]], H1, H2),
    elimina([], H2, Novas_Folhas).

rou_e([X ==> Y], Folhas, Novas_Folhas) :-
    membro(A ou B, X),
    elimina(A ou B, X, X1),
    elimina([X ==> Y], Folhas, H1),
    append([[[A|X1] ==> Y], [[B|X1] ==> Y]], H1, H2),
    elimina([], H2, Novas_Folhas).

/*Aplica��o das regras acima definidas.*/
apl_reg(rneg_e, S, Folhas, Novas_Folhas):- rneg_e(S, Folhas, Novas_Folhas).
apl_reg(rneg_d, S, Folhas, Novas_Folhas):- rneg_d(S, Folhas, Novas_Folhas).
apl_reg(rimp_e, S, Folhas, Novas_Folhas):- rimp_e(S, Folhas, Novas_Folhas).
apl_reg(rimp_d, S, Folhas, Novas_Folhas):- rimp_d(S, Folhas, Novas_Folhas).
apl_reg(re_e, S, Folhas, Novas_Folhas):- re_e(S, Folhas, Novas_Folhas).
apl_reg(re_d, S, Folhas, Novas_Folhas):- re_d(S, Folhas, Novas_Folhas).
apl_reg(rou_e, S, Folhas, Novas_Folhas):- rou_e(S, Folhas, Novas_Folhas).
apl_reg(rou_d, S, Folhas, Novas_Folhas):- rou_d(S, Folhas, Novas_Folhas).

/*tem_conectivos/1 : Dado um sequente X ==> Y, este predicado verifica se X ou Y cont�m algum conectivo.*/
tem_conectivos(X ==> Y) :- membro(neg _, X).
tem_conectivos(X ==> Y) :- membro(neg _, Y).
tem_conectivos(X ==> Y) :- membro(_ e _, X).
tem_conectivos(X ==> Y) :- membro(_ e _, Y).
tem_conectivos(X ==> Y) :- membro(_ ou _, X).
tem_conectivos(X ==> Y) :- membro(_ ou _, Y).
tem_conectivos(X ==> Y) :- membro(_ imp _, X).
tem_conectivos(X ==> Y) :- membro(_ imp _, Y).

/*arv_esgotada/1 : Verifica se todas as folhas s�o axiomas ou n�o tem conectivos.*/
arv_esgotada([]).
arv_esgotada([[X ==> Y]|R]) :- axioma(X ==> Y), arv_esgotada(R).
arv_esgotada([[X ==> Y]|R]) :- not(tem_conectivos(X ==> Y)), arv_esgotada(R).

/*enesimo/3 : tal que enesimo(N, L, X) tem o valor verdadeiro se o elemento X est� na posi��o N da lista L.*/
enesimo(1,[X|L],X).
enesimo(N,[X|L],Y):-enesimo(N1,L,Y), N is N1+1.

/*escrever_folhas/2 : Lista as folhas e as suas posi��es correspondentes para facilitar a sele��o ao utilizador.*/
escrever_folhas([], Folhas).
escrever_folhas([H|T], Folhas):-
    enesimo(N, Folhas, H),
    write(N),
    write(" : "),
    writeln(H),
    escrever_folhas(T, Folhas).

/*aux_ajuda/1 : Predicado auxiliar usado pelo ajuda_sp, cujo objetivo � a demonstra��o das folhas atuais da �rvore, escolha da folha a qual aplicar a regra.*/
aux_ajuda(Folhas) :-
    arv_esgotada(Folhas),
    writeln("As folhas neste momento s�o:"),
    escrever_folhas(Folhas, Folhas),
    writeln("��rvore esgotada. Execu��o terminada!").
aux_ajuda(Folhas) :-
    not(arv_esgotada(Folhas)),
    writeln("As folhas neste momento s�o:"),
    escrever_folhas(Folhas, Folhas),
    writeln("Escreva o n�mero correspondente � folha a que deseja aplicar a regra."),
    read(N_escolhida),
    enesimo(N_escolhida, Folhas, F_escolhida),
    write("Folha selecionada:"),
    writeln(F_escolhida),
    writeln("Escreva a regra que pretende aplicar (rneg_e, rneg_d, rimp_e, rimp_d, re_e, re_d, rou_e, rou_d):"),
    read(Regra),
    apl_reg(Regra, F_escolhida, Folhas, Novas_Folhas),
    aux_ajuda(Novas_Folhas).

/*ajuda_sp/0 : Recebe um sequente e inicia o processo de constru��o da �rvore.*/
ajuda_sp :-
    writeln('Redija o sequente que pretende analisar:'),
    read(Sequente),
    aux_ajuda([Sequente]).
