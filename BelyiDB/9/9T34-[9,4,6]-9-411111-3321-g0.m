s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[9,4,6]-9-411111-3321-g0";
s`BelyiDBFilename := "9T34-[9,4,6]-9-411111-3321-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 8, 9, 3, 4, 5, 1, 7, 2 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
[ 7, 9, 3, 5, 6, 4, 8, 1, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 8, 9, 3, 4, 5, 1, 7, 2 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 7, 9, 3, 5, 6, 4, 8, 1, 2 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 8, 9, 3, 4, 5, 1, 7, 2 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 7, 9, 3, 5, 6, 4, 8, 1, 2 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 6, 8, 9, 3, 4, 5, 1, 7, 2 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 7, 9, 3, 5, 6, 4, 8, 1, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 7, 2, 1, 3, 5, 6, 4, 8, 9 ],
[ 9, 3, 2, 4, 7, 5, 6, 1, 8 ]
],
[ PermutationGroup<9 |  
\[ 6, 8, 9, 3, 4, 5, 1, 7, 2 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 7, 9, 3, 5, 6, 4, 8, 1, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 7, 2, 3, 1, 4, 6, 5, 8, 9 ],
[ 9, 4, 2, 3, 5, 7, 6, 1, 8 ]
],
[ PermutationGroup<9 |  
\[ 6, 8, 9, 3, 4, 5, 1, 7, 2 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
\[ 7, 9, 3, 5, 6, 4, 8, 1, 2 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 8, 2, 3, 1, 4, 6, 7, 5, 9 ],
[ 9, 4, 2, 3, 5, 8, 6, 7, 1 ]
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
[ 6, 8, 9, 3, 4, 5, 1, 7, 2 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
[ 7, 9, 3, 5, 6, 4, 8, 1, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 9, 8, 3, 4, 5, 2, 7, 1 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
[ 9, 7, 3, 5, 6, 4, 8, 2, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 8, 2, 9, 4, 5, 1, 7, 3 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ],
[ 7, 2, 9, 5, 6, 4, 8, 1, 3 ]
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
