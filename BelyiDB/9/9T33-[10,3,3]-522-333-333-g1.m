s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[10,3,3]-522-333-333-g1";
s`BelyiDBFilename := "9T33-[10,3,3]-522-333-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 10, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 5, 9, 2, 8, 7, 6, 1, 3 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 6, 8, 3, 1, 9, 5, 4, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 9, 2, 8, 7, 6, 1, 3 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 6, 8, 3, 1, 9, 5, 4, 2 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 9, 2, 8, 7, 6, 1, 3 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 6, 8, 3, 1, 9, 5, 4, 2 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 9, 2, 8, 7, 6, 1, 3 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 6, 8, 3, 1, 9, 5, 4, 2 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 3, 4, 9, 6, 8, 2, 5, 7, 1 ],
[ 7, 9, 6, 1, 2, 8, 4, 3, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 5, 9, 2, 8, 7, 6, 1, 3 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 6, 8, 3, 1, 9, 5, 4, 2 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
