s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T20-[9,6,6]-9-3222-63-g2";
s`BelyiDBFilename := "9T20-[9,6,6]-9-3222-63-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 162 > |
[ 4, 5, 7, 8, 6, 1, 2, 9, 3 ],
[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
[ 2, 9, 7, 8, 6, 3, 4, 5, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 9, 1, 5, 3, 4, 8, 6, 7, 2 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 7, 8, 6, 1, 2, 9, 3 ],
\[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
\[ 2, 9, 7, 8, 6, 3, 4, 5, 1 ]:
 Order := 162 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 7, 8, 6, 1, 2, 9, 3 ],
\[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
\[ 2, 9, 7, 8, 6, 3, 4, 5, 1 ]:
 Order := 162 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 7, 8, 6, 1, 2, 9, 3 ],
\[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
\[ 2, 9, 7, 8, 6, 3, 4, 5, 1 ]:
 Order := 162 > |
[ 6, 7, 9, 1, 2, 5, 3, 4, 8 ],
[ 5, 3, 2, 9, 1, 7, 8, 6, 4 ],
[ 9, 1, 6, 7, 8, 5, 3, 4, 2 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 7, 8, 6, 1, 2, 9, 3 ],
\[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
\[ 2, 9, 7, 8, 6, 3, 4, 5, 1 ]:
 Order := 162 > |
[ 6, 7, 9, 1, 2, 5, 3, 4, 8 ],
[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
[ 5, 3, 9, 1, 2, 8, 6, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 7, 8, 6, 1, 2, 9, 3 ],
\[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
\[ 2, 9, 7, 8, 6, 3, 4, 5, 1 ]:
 Order := 162 > |
[ 6, 7, 9, 1, 2, 5, 3, 4, 8 ],
[ 9, 1, 6, 7, 8, 3, 4, 5, 2 ],
[ 7, 8, 4, 5, 3, 2, 9, 1, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 162 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 162 > |
[ 4, 5, 7, 8, 6, 1, 2, 9, 3 ],
[ 8, 6, 5, 3, 4, 2, 9, 1, 7 ],
[ 2, 9, 7, 8, 6, 3, 4, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 162 > |
[ 5, 3, 7, 8, 6, 2, 9, 1, 4 ],
[ 6, 7, 5, 3, 4, 1, 2, 9, 8 ],
[ 9, 1, 7, 8, 6, 3, 4, 5, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 162 > |
[ 4, 5, 8, 6, 7, 9, 1, 2, 3 ],
[ 8, 6, 4, 5, 3, 2, 9, 1, 7 ],
[ 9, 1, 7, 8, 6, 3, 4, 5, 2 ]
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
