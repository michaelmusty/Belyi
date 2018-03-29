s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,5,6]-63-51111-3321-g0";
s`BelyiDBFilename := "9T34-[6,5,6]-63-51111-3321-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 5, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
\[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
\[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
\[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 2, 1, 4, 5, 3, 7, 6, 8 ],
[ 8, 3, 2, 6, 4, 5, 1, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
\[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 4, 1, 3, 8, 5, 6, 7, 9, 2 ],
[ 6, 2, 9, 3, 1, 5, 8, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
\[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 5, 9, 3, 4, 2, 6, 7, 1, 8 ],
[ 6, 8, 5, 3, 4, 1, 2, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
\[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
\[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 1, 2, 6, 4, 7, 5, 8, 3, 9 ],
[ 3, 1, 2, 8, 4, 6, 9, 5, 7 ]
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
[ 3, 4, 2, 6, 7, 9, 8, 5, 1 ],
[ 1, 9, 3, 4, 2, 8, 7, 5, 6 ],
[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 1, 2, 3, 4, 7, 8, 6, 5 ],
[ 4, 2, 3, 8, 5, 9, 7, 6, 1 ],
[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 7, 2, 6, 1, 9, 8, 5, 4 ],
[ 1, 5, 3, 4, 9, 8, 7, 2, 6 ],
[ 2, 3, 1, 5, 6, 4, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 1, 2, 3, 6, 4, 9, 7, 8 ],
[ 7, 6, 3, 4, 5, 1, 8, 2, 9 ],
[ 8, 3, 4, 2, 6, 5, 7, 9, 1 ]
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
