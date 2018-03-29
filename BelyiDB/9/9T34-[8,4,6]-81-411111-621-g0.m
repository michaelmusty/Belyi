s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,4,6]-81-411111-621-g0";
s`BelyiDBFilename := "9T34-[8,4,6]-81-411111-621-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
\[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
\[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
\[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
\[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
\[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
\[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 8, 3, 4, 5, 6, 7, 9, 1 ],
[ 1, 3, 4, 5, 6, 7, 2, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
\[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
\[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 3, 2, 4, 9, 5, 6, 7, 8, 1 ],
[ 2, 1, 3, 5, 6, 7, 8, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
\[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
\[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 9, 1, 4, 5, 6, 7, 8, 3 ],
[ 1, 9, 4, 5, 6, 7, 8, 3, 2 ]
],
[ PermutationGroup<9 |  
\[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
\[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
\[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 2, 4, 3, 9, 5, 6, 7, 8, 1 ],
[ 1, 3, 2, 5, 6, 7, 8, 9, 4 ]
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
[ 6, 7, 2, 3, 4, 5, 9, 8, 1 ],
[ 1, 9, 3, 4, 5, 6, 8, 2, 7 ],
[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 1, 2, 3, 4, 5, 6, 8, 7 ],
[ 7, 2, 3, 4, 5, 6, 8, 9, 1 ],
[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 1, 2, 4, 7, 5, 8, 9, 3 ],
[ 1, 2, 3, 9, 4, 6, 7, 5, 8 ],
[ 2, 3, 4, 5, 6, 1, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 1, 2, 3, 4, 5, 6, 7, 9 ],
[ 9, 2, 3, 4, 5, 8, 7, 1, 6 ],
[ 2, 3, 4, 5, 9, 7, 6, 8, 1 ]
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
