s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T10-[9,6,6]-9-621-621-g2";
s`BelyiDBFilename := "9T10-[9,6,6]-9-621-621-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 8, 7, 6, 5, 4, 3, 2, 1, 9 ]:
 Order := 54 > |
[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
\[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
\[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]:
 Order := 54 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
\[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
\[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]:
 Order := 54 >) |
[ PermutationGroup<9 |  
\[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
\[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
\[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]:
 Order := 54 > |
[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]
],
[ PermutationGroup<9 |  
\[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
\[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
\[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]:
 Order := 54 > |
[ 2, 6, 1, 5, 9, 4, 8, 3, 7 ],
[ 4, 9, 5, 1, 6, 2, 7, 3, 8 ],
[ 8, 4, 9, 5, 1, 6, 2, 7, 3 ]
],
[ PermutationGroup<9 |  
\[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
\[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
\[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]:
 Order := 54 > |
[ 8, 9, 1, 2, 3, 4, 5, 6, 7 ],
[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
[ 5, 1, 6, 2, 7, 3, 8, 4, 9 ]
],
[ PermutationGroup<9 |  
\[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
\[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
\[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]:
 Order := 54 > |
[ 8, 9, 1, 2, 3, 4, 5, 6, 7 ],
[ 4, 9, 5, 1, 6, 2, 7, 3, 8 ],
[ 8, 1, 3, 5, 7, 9, 2, 4, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 8, 7, 6, 5, 4, 3, 2, 1, 9 ]:
 Order := 54 >) |
[ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 8, 7, 6, 5, 4, 3, 2, 1, 9 ]:
 Order := 54 > |
[ 9, 7, 5, 3, 1, 8, 6, 4, 2 ],
[ 4, 6, 8, 1, 3, 5, 7, 9, 2 ],
[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]
],
[ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 8, 7, 6, 5, 4, 3, 2, 1, 9 ]:
 Order := 54 > |
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 4, 9, 5, 1, 6, 2, 7, 3, 8 ],
[ 6, 8, 1, 3, 5, 7, 9, 2, 4 ]
],
[ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 8, 7, 6, 5, 4, 3, 2, 1, 9 ]:
 Order := 54 > |
[ 3, 7, 2, 6, 1, 5, 9, 4, 8 ],
[ 4, 9, 5, 1, 6, 2, 7, 3, 8 ],
[ 3, 8, 4, 9, 5, 1, 6, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 4, 8, 3, 7, 2, 6, 1, 5, 9 ],
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 8, 7, 6, 5, 4, 3, 2, 1, 9 ]:
 Order := 54 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 3, 5, 7, 9, 2, 4, 6, 8, 1 ],
[ 4, 9, 5, 1, 6, 2, 7, 3, 8 ]
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
