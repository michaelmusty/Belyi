s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T20-[9,6,6]-9-63-6111-g2";
s`BelyiDBFilename := "9T20-[9,6,6]-9-63-6111-g2.m";
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
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 9, 1, 5, 3, 4, 8, 6, 7, 2 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 9, 1, 5, 3, 4, 8, 6, 7, 2 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]:
 Order := 162 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]:
 Order := 162 >) |
[ PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]:
 Order := 162 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]:
 Order := 162 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 7, 8, 5, 3, 4, 1, 2, 9, 6 ],
[ 1, 2, 7, 8, 6, 4, 5, 3, 9 ]
],
[ PermutationGroup<9 |  
\[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
\[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
\[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]:
 Order := 162 > |
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 7, 8, 4, 5, 3, 2, 9, 1, 6 ],
[ 1, 2, 6, 7, 8, 5, 3, 4, 9 ]
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
[ 5, 3, 6, 7, 8, 9, 1, 2, 4 ],
[ 9, 1, 8, 6, 7, 3, 4, 5, 2 ],
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 162 > |
[ 3, 4, 7, 8, 6, 2, 9, 1, 5 ],
[ 2, 9, 6, 7, 8, 5, 3, 4, 1 ],
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 162 > |
[ 5, 3, 7, 8, 6, 9, 1, 2, 4 ],
[ 9, 1, 8, 6, 7, 5, 3, 4, 2 ],
[ 5, 3, 9, 1, 2, 6, 7, 8, 4 ]
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
