s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,3]-63-3321-333-g1";
s`BelyiDBFilename := "9T34-[6,6,3]-63-3321-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
\[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
\[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
\[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 7, 5, 2, 6, 3, 4, 8, 1 ],
[ 5, 9, 4, 6, 7, 3, 1, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
\[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 3, 5, 8, 2, 4, 7, 6, 1 ],
[ 8, 9, 5, 2, 6, 3, 1, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
\[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 9, 1, 4, 6, 8, 2, 5, 7 ],
[ 5, 3, 7, 1, 4, 8, 2, 9, 6 ]
],
[ PermutationGroup<9 |  
\[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
\[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 3, 8, 1, 5, 7, 6, 4, 9, 2 ],
[ 6, 3, 9, 1, 7, 4, 8, 5, 2 ]
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
[ 5, 9, 1, 8, 4, 3, 2, 6, 7 ],
[ 2, 3, 1, 6, 5, 4, 8, 9, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 3, 1, 6, 9, 2, 4, 5, 8 ],
[ 5, 7, 6, 2, 1, 8, 4, 3, 9 ],
[ 8, 3, 4, 2, 6, 7, 5, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 9, 7, 2, 3, 1, 6, 5, 4 ],
[ 2, 6, 8, 5, 9, 1, 7, 3, 4 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 4, 6, 3, 7, 8, 9, 1, 5 ],
[ 4, 8, 1, 3, 2, 9, 7, 5, 6 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]
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
