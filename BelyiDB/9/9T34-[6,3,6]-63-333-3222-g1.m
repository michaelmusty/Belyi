s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,3,6]-63-333-3222-g1";
s`BelyiDBFilename := "9T34-[6,3,6]-63-333-3222-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 3, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 9, 6, 2, 3, 7, 1, 5, 4 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 9, 6, 4, 8, 7, 2, 5, 3, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 9, 6, 2, 3, 7, 1, 5, 4 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 9, 6, 4, 8, 7, 2, 5, 3, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 9, 6, 2, 3, 7, 1, 5, 4 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 9, 6, 4, 8, 7, 2, 5, 3, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 8, 9, 6, 2, 3, 7, 1, 5, 4 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
\[ 9, 6, 4, 8, 7, 2, 5, 3, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 4, 8, 5, 9, 7, 2, 3, 6, 1 ],
[ 8, 9, 6, 7, 1, 3, 4, 5, 2 ]
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
[ 8, 9, 6, 2, 3, 7, 1, 5, 4 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ],
[ 9, 6, 4, 8, 7, 2, 5, 3, 1 ]
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
