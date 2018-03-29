s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[7,12,2]-711-432-22221-g0";
s`BelyiDBFilename := "9T33-[7,12,2]-711-432-22221-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 7, 12, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
\[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
\[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
\[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
\[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
\[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
\[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 4, 3, 9, 1, 7, 5, 8, 6, 2 ],
[ 5, 4, 9, 2, 1, 6, 8, 7, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
\[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
\[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 2, 9, 7, 5, 4, 3, 8, 6, 1 ],
[ 3, 9, 1, 6, 5, 4, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
\[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
\[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 2, 1, 7, 5, 9, 3, 8, 6, 4 ],
[ 3, 2, 1, 6, 9, 4, 8, 7, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
\[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
\[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 9, 1, 6, 5, 8, 3, 2, 4, 7 ],
[ 9, 2, 7, 6, 8, 4, 3, 5, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 5, 4, 2, 9, 1, 7, 8, 6, 3 ],
[ 6, 5, 3, 9, 2, 1, 8, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 5, 4, 9, 3, 1, 7, 8, 6, 2 ],
[ 6, 5, 9, 4, 2, 1, 8, 7, 3 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 5, 9, 4, 3, 2, 7, 8, 6, 1 ],
[ 6, 9, 5, 4, 3, 1, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 5, 6, 7, 1, 8, 9 ],
[ 5, 3, 2, 1, 9, 7, 8, 6, 4 ],
[ 6, 4, 3, 2, 9, 1, 8, 7, 5 ]
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
