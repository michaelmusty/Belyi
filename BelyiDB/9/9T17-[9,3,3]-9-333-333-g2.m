s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T17-[9,3,3]-9-333-333-g2";
s`BelyiDBFilename := "9T17-[9,3,3]-9-333-333-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 3, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 > |
[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 9, 1, 5, 3, 4, 8, 6, 7, 2 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 9, 1, 5, 3, 4, 8, 6, 7, 2 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
\[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
\[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 >) |
[ PermutationGroup<9 |  
\[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
\[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 > |
[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
\[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 > |
[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
[ 9, 1, 4, 5, 3, 8, 6, 7, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 > |
[ 8, 6, 1, 2, 9, 5, 3, 4, 7 ],
[ 9, 1, 5, 3, 4, 7, 8, 6, 2 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 81 > |
[ 4, 5, 6, 7, 8, 2, 9, 1, 3 ],
[ 6, 7, 2, 9, 1, 5, 3, 4, 8 ],
[ 9, 1, 4, 5, 3, 7, 8, 6, 2 ]
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
