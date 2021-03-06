s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T23-[6,6,4]-621-621-441-g1";
s`BelyiDBFilename := "9T23-[6,6,4]-621-621-441-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
\[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
\[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]:
 Order := 216 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
\[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
\[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]:
 Order := 216 >) |
[ PermutationGroup<9 |  
\[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
\[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
\[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 6, 3, 4, 1, 7, 8, 5, 2, 9 ],
[ 3, 8, 5, 7, 9, 6, 2, 4, 1 ]
],
[ PermutationGroup<9 |  
\[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
\[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
\[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 3, 5, 2, 1, 9, 6, 8, 7, 4 ],
[ 9, 3, 8, 2, 5, 7, 1, 4, 6 ]
],
[ PermutationGroup<9 |  
\[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
\[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
\[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 4, 9, 5, 1, 6, 2, 7, 3, 8 ],
[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]
],
[ PermutationGroup<9 |  
\[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
\[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
\[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 6, 5, 7, 3, 2, 4, 9, 8, 1 ],
[ 6, 5, 3, 2, 7, 8, 4, 9, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 5, 4, 1, 9, 2, 8, 7, 6, 3 ],
[ 2, 5, 7, 1, 4, 6, 9, 3, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 4, 1, 2, 8, 5, 3, 9, 6, 7 ],
[ 1, 3, 9, 5, 7, 4, 6, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 2, 7, 9, 8, 4, 6, 5, 1, 3 ],
[ 5, 1, 2, 7, 3, 4, 9, 8, 6 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ],
\[ 1, 2, 4, 5, 3, 8, 6, 7, 9 ]:
 Order := 216 > |
[ 8, 2, 7, 1, 4, 9, 3, 6, 5 ],
[ 9, 8, 1, 6, 5, 7, 3, 2, 4 ],
[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ]
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
