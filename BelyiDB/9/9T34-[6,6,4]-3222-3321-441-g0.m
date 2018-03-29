s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,4]-3222-3321-441-g0";
s`BelyiDBFilename := "9T34-[6,6,4]-3222-3321-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
\[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
\[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
\[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
\[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
\[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
\[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]:
 Order := 362880 > |
[ 3, 9, 1, 5, 6, 4, 8, 7, 2 ],
[ 6, 3, 9, 1, 7, 4, 5, 8, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
\[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
\[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]:
 Order := 362880 > |
[ 2, 1, 5, 6, 3, 4, 8, 9, 7 ],
[ 6, 2, 1, 5, 7, 3, 4, 9, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
\[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
\[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]:
 Order := 362880 > |
[ 5, 9, 1, 6, 3, 4, 8, 7, 2 ],
[ 6, 3, 9, 5, 7, 1, 4, 8, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
\[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
\[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]:
 Order := 362880 > |
[ 8, 5, 9, 2, 4, 7, 6, 1, 3 ],
[ 5, 8, 4, 9, 1, 2, 7, 6, 3 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
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
[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
[ 7, 4, 1, 2, 5, 8, 3, 9, 6 ],
[ 7, 3, 4, 5, 2, 6, 8, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 1, 5, 4, 8, 9, 6, 7 ],
[ 7, 3, 2, 9, 5, 4, 8, 1, 6 ],
[ 2, 8, 3, 5, 6, 7, 4, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 1, 6, 3, 4, 8, 7, 2 ],
[ 6, 3, 9, 5, 7, 1, 4, 8, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 8, 1, 3, 6, 5, 9, 2, 7 ],
[ 7, 3, 8, 9, 1, 6, 5, 2, 4 ],
[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]
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
