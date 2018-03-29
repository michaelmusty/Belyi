s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,5,6]-63-51111-3222-g0";
s`BelyiDBFilename := "9T34-[6,5,6]-63-51111-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 5, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 2, 5, 6, 1, 8, 9, 7 ],
[ 1, 6, 3, 4, 2, 9, 5, 8, 7 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 1, 8, 9, 7 ],
\[ 1, 6, 3, 4, 2, 9, 5, 8, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 1, 8, 9, 7 ],
\[ 1, 6, 3, 4, 2, 9, 5, 8, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 1, 8, 9, 7 ],
\[ 1, 6, 3, 4, 2, 9, 5, 8, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 1, 2, 6, 4, 3, 7, 8, 5, 9 ],
[ 3, 1, 2, 5, 4, 8, 9, 6, 7 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 1, 8, 9, 7 ],
\[ 1, 6, 3, 4, 2, 9, 5, 8, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 1, 6, 3, 4, 2, 7, 8, 5, 9 ],
[ 2, 1, 5, 3, 4, 8, 9, 6, 7 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 2, 5, 6, 1, 8, 9, 7 ],
\[ 1, 6, 3, 4, 2, 9, 5, 8, 7 ],
\[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 1, 9, 3, 2, 5, 4, 6, 8, 7 ],
[ 7, 1, 4, 3, 6, 5, 2, 9, 8 ]
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
[ 3, 4, 2, 5, 6, 1, 8, 9, 7 ],
[ 1, 6, 3, 4, 2, 9, 5, 8, 7 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 2, 8, 6, 7, 5, 9, 1 ],
[ 1, 9, 3, 7, 2, 6, 5, 8, 4 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 4, 6, 5, 2, 7, 8, 9, 1 ],
[ 1, 9, 5, 4, 2, 6, 3, 8, 7 ],
[ 2, 3, 1, 5, 4, 7, 6, 9, 8 ]
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
