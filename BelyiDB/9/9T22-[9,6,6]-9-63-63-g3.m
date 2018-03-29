s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T22-[9,6,6]-9-63-63-g3";
s`BelyiDBFilename := "9T22-[9,6,6]-9-63-63-g3.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 > |
[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
\[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
\[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]:
 Order := 162 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
\[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
\[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]:
 Order := 162 >) |
[ PermutationGroup<9 |  
\[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
\[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
\[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]:
 Order := 162 > |
[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
\[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
\[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]:
 Order := 162 > |
[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
[ 4, 3, 7, 6, 8, 1, 9, 2, 5 ],
[ 5, 4, 6, 8, 7, 2, 1, 9, 3 ]
],
[ PermutationGroup<9 |  
\[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
\[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
\[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]:
 Order := 162 > |
[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
[ 3, 5, 6, 8, 7, 1, 9, 2, 4 ],
[ 4, 3, 6, 8, 7, 1, 9, 2, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 > |
[ 3, 4, 6, 7, 8, 2, 9, 1, 5 ],
[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
[ 4, 3, 8, 7, 6, 2, 1, 9, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 > |
[ 4, 5, 7, 8, 6, 9, 1, 2, 3 ],
[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 162 > |
[ 5, 3, 6, 7, 8, 1, 2, 9, 4 ],
[ 4, 3, 6, 8, 7, 9, 2, 1, 5 ],
[ 3, 5, 7, 6, 8, 2, 1, 9, 4 ]
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
