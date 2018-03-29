s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T4-[6,6,3]-63-63-333-g2";
s`BelyiDBFilename := "9T4-[6,6,3]-63-63-333-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 6, 8, 1, 9, 2, 4, 3, 5, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 3 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]:
 Order := 3 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 6, 8, 1, 9, 2, 4, 3, 5, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 18 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 6, 8, 1, 9, 2, 4, 3, 5, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 18 >) |
[ PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 6, 8, 1, 9, 2, 4, 3, 5, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 3, 5, 7, 6, 8, 1, 9, 2, 4 ],
[ 5, 3, 7, 8, 6, 1, 2, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
\[ 6, 8, 1, 9, 2, 4, 3, 5, 7 ],
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 6, 8, 1, 9, 2, 4, 3, 5, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 18 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 6, 8, 1, 9, 2, 4, 3, 5, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 18 > |
[ 5, 4, 6, 8, 7, 9, 2, 1, 3 ],
[ 3, 5, 7, 6, 8, 1, 9, 2, 4 ],
[ 5, 3, 7, 8, 6, 1, 2, 9, 4 ]
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
