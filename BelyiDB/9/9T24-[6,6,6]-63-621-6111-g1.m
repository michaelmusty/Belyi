s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T24-[6,6,6]-63-621-6111-g1";
s`BelyiDBFilename := "9T24-[6,6,6]-63-621-6111-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 324 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 5, 4, 1, 9, 2, 6, 8, 7, 3 ],
[ 8, 6, 3, 4, 5, 9, 1, 2, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
\[ 5, 4, 1, 9, 2, 6, 8, 7, 3 ],
\[ 8, 6, 3, 4, 5, 9, 1, 2, 7 ]:
 Order := 324 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
\[ 5, 4, 1, 9, 2, 6, 8, 7, 3 ],
\[ 8, 6, 3, 4, 5, 9, 1, 2, 7 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
\[ 5, 4, 1, 9, 2, 6, 8, 7, 3 ],
\[ 8, 6, 3, 4, 5, 9, 1, 2, 7 ]:
 Order := 324 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 5, 4, 1, 9, 2, 6, 8, 7, 3 ],
[ 8, 6, 3, 4, 5, 9, 1, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
\[ 5, 4, 1, 9, 2, 6, 8, 7, 3 ],
\[ 8, 6, 3, 4, 5, 9, 1, 2, 7 ]:
 Order := 324 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 4, 3, 1, 9, 2, 7, 6, 8, 5 ],
[ 6, 7, 3, 4, 5, 2, 9, 1, 8 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 324 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 324 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 5, 4, 1, 9, 2, 6, 8, 7, 3 ],
[ 8, 6, 3, 4, 5, 9, 1, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 5, 4, 6, 8, 7, 9 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 1, 2, 6, 7, 8, 3, 4, 5, 9 ]:
 Order := 324 > |
[ 3, 5, 6, 8, 7, 2, 1, 9, 4 ],
[ 2, 1, 7, 6, 8, 3, 5, 4, 9 ],
[ 3, 4, 2, 9, 1, 6, 7, 8, 5 ]
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
