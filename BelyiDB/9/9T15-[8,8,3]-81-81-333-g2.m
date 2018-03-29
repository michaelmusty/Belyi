s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T15-[8,8,3]-81-81-333-g2";
s`BelyiDBFilename := "9T15-[8,8,3]-81-81-333-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 8, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 9, 5, 8, 1, 3, 6, 2, 4, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 9, 5, 8, 1, 3, 6, 2, 4, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 72 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 9, 5, 8, 1, 3, 6, 2, 4, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 72 >) |
[ PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 9, 5, 8, 1, 3, 6, 2, 4, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 72 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 3, 8, 2, 4, 6, 9, 5, 7, 1 ],
[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]
],
[ PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 9, 5, 8, 1, 3, 6, 2, 4, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 72 > |
[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
[ 5, 9, 6, 4, 2, 8, 3, 1, 7 ],
[ 9, 1, 5, 3, 4, 8, 6, 7, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 9, 5, 8, 1, 3, 6, 2, 4, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
[ 9, 7, 4, 2, 6, 3, 1, 8, 5 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
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
