s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T25-[9,9,9]-9-9-9-g4";
s`BelyiDBFilename := "9T25-[9,9,9]-9-9-9-g4.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 9, 9 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 4;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
\[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]:
 Order := 324 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
\[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
\[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
\[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 4, 3, 7, 8, 6, 1, 9, 2, 5 ],
[ 3, 4, 8, 7, 6, 2, 1, 9, 5 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
\[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 3, 4, 7, 6, 8, 9, 2, 1, 5 ],
[ 3, 5, 7, 6, 8, 1, 2, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
\[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 4, 3, 7, 6, 8, 2, 9, 1, 5 ],
[ 3, 5, 6, 7, 8, 2, 1, 9, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 4, 3, 6, 7, 8, 9, 2, 1, 5 ],
[ 4, 5, 7, 6, 8, 2, 1, 9, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 3, 5, 6, 8, 7, 2, 9, 1, 4 ],
[ 5, 4, 6, 7, 8, 1, 9, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 5, 4, 6, 8, 7, 1, 2, 9, 3 ],
[ 5, 4, 7, 8, 6, 9, 2, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 1, 2, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 324 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 5, 4, 7, 8, 6, 2, 1, 9, 3 ],
[ 3, 4, 6, 8, 7, 9, 2, 1, 5 ]
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
