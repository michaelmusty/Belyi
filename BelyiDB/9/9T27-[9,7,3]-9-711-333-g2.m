s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T27-[9,7,3]-9-711-333-g2";
s`BelyiDBFilename := "9T27-[9,7,3]-9-711-333-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 7, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 > |
[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
[ 8, 7, 3, 5, 2, 6, 9, 4, 1 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
\[ 8, 7, 3, 5, 2, 6, 9, 4, 1 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
\[ 8, 7, 3, 5, 2, 6, 9, 4, 1 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 >) |
[ PermutationGroup<9 |  
\[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
\[ 8, 7, 3, 5, 2, 6, 9, 4, 1 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 > |
[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
[ 5, 8, 3, 2, 4, 9, 7, 6, 1 ],
[ 5, 8, 4, 7, 6, 1, 3, 9, 2 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
\[ 8, 7, 3, 5, 2, 6, 9, 4, 1 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 > |
[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
[ 8, 9, 3, 4, 1, 2, 5, 6, 7 ],
[ 4, 8, 6, 9, 2, 7, 3, 5, 1 ]
],
[ PermutationGroup<9 |  
\[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
\[ 8, 7, 3, 5, 2, 6, 9, 4, 1 ],
\[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]:
 Order := 504 > |
[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
[ 9, 5, 6, 4, 7, 2, 1, 8, 3 ],
[ 4, 3, 6, 5, 1, 2, 9, 7, 8 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 >) |
[ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 > |
[ 8, 3, 7, 1, 6, 2, 4, 9, 5 ],
[ 8, 7, 3, 5, 2, 6, 9, 4, 1 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 > |
[ 9, 1, 6, 8, 3, 7, 4, 2, 5 ],
[ 1, 7, 6, 3, 5, 8, 9, 2, 4 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ],
\[ 2, 4, 6, 3, 1, 7, 5, 8, 9 ],
\[ 1, 5, 6, 7, 2, 3, 4, 9, 8 ]:
 Order := 504 > |
[ 9, 3, 5, 7, 6, 4, 1, 2, 8 ],
[ 1, 6, 4, 5, 2, 8, 3, 7, 9 ],
[ 8, 6, 5, 2, 7, 4, 3, 9, 1 ]
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
