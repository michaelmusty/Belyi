s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T1-[9,9,3]-9-9-333-g3";
s`BelyiDBFilename := "9T1-[9,9,3]-9-9-333-g3.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 9, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 6, 7, 8, 9, 1, 2, 3, 4, 5 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 6, 7, 8, 9, 1, 2, 3, 4, 5 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 9 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 6, 7, 8, 9, 1, 2, 3, 4, 5 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 9 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 6, 7, 8, 9, 1, 2, 3, 4, 5 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 6, 7, 8, 9, 1, 2, 3, 4, 5 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 6, 7, 8, 9, 1, 2, 3, 4, 5 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 3, 4, 5, 6, 7, 8, 9, 1, 2 ],
[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 6, 7, 8, 9, 1, 2, 3, 4, 5 ],
[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 3, 4, 5, 6, 7, 8, 9, 1, 2 ],
[ 7, 8, 9, 1, 2, 3, 4, 5, 6 ]
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
