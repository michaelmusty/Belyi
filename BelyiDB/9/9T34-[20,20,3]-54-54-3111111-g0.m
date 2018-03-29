s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[20,20,3]-54-54-3111111-g0";
s`BelyiDBFilename := "9T34-[20,20,3]-54-54-3111111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 20, 20, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 7, 4, 5, 6, 3, 8, 9, 1 ],
[ 6, 9, 1, 3, 4, 5, 2, 7, 8 ],
[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 7, 4, 5, 6, 3, 8, 9, 1 ],
\[ 6, 9, 1, 3, 4, 5, 2, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 7, 4, 5, 6, 3, 8, 9, 1 ],
\[ 6, 9, 1, 3, 4, 5, 2, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 7, 4, 5, 6, 3, 8, 9, 1 ],
\[ 6, 9, 1, 3, 4, 5, 2, 7, 8 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 6, 5, 2, 3, 4, 9, 1, 7, 8 ],
[ 2, 7, 3, 4, 5, 6, 1, 8, 9 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 7, 4, 5, 6, 3, 8, 9, 1 ],
[ 6, 9, 1, 3, 4, 5, 2, 7, 8 ],
[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]
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
