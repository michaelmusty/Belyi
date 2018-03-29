s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[20,3,6]-54-333-3222-g1";
s`BelyiDBFilename := "9T34-[20,3,6]-54-333-3222-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 20, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 7, 4, 9, 3, 8, 6, 1, 5 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 3, 4, 2, 8, 9, 1, 5, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 7, 4, 9, 3, 8, 6, 1, 5 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 3, 4, 2, 8, 9, 1, 5, 6 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 7, 4, 9, 3, 8, 6, 1, 5 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 3, 4, 2, 8, 9, 1, 5, 6 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 7, 4, 9, 3, 8, 6, 1, 5 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 7, 3, 4, 2, 8, 9, 1, 5, 6 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 8, 9, 6 ],
[ 2, 8, 5, 9, 6, 3, 4, 1, 7 ],
[ 3, 8, 1, 6, 7, 4, 5, 9, 2 ]
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
[ 2, 7, 4, 9, 3, 8, 6, 1, 5 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 7, 3, 4, 2, 8, 9, 1, 5, 6 ]
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
