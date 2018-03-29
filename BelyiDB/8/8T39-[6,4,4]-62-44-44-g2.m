s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T39-[6,4,4]-62-44-44-g2";
s`BelyiDBFilename := "8T39-[6,4,4]-62-44-44-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 4, 6, 5, 2, 1, 3, 8, 7 ],
[ 3, 8, 5, 2, 7, 4, 1, 6 ],
[ 3, 6, 8, 7, 1, 4, 2, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 6, 5, 2, 1, 3, 8, 7 ],
\[ 3, 8, 5, 2, 7, 4, 1, 6 ],
\[ 3, 6, 8, 7, 1, 4, 2, 5 ]:
 Order := 192 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 6, 5, 2, 1, 3, 8, 7 ],
\[ 3, 8, 5, 2, 7, 4, 1, 6 ],
\[ 3, 6, 8, 7, 1, 4, 2, 5 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 4, 6, 5, 2, 1, 3, 8, 7 ],
\[ 3, 8, 5, 2, 7, 4, 1, 6 ],
\[ 3, 6, 8, 7, 1, 4, 2, 5 ]:
 Order := 192 > |
[ 4, 6, 5, 2, 1, 3, 8, 7 ],
[ 3, 8, 5, 2, 7, 4, 1, 6 ],
[ 3, 6, 8, 7, 1, 4, 2, 5 ]
],
[ PermutationGroup<8 |  
\[ 4, 6, 5, 2, 1, 3, 8, 7 ],
\[ 3, 8, 5, 2, 7, 4, 1, 6 ],
\[ 3, 6, 8, 7, 1, 4, 2, 5 ]:
 Order := 192 > |
[ 4, 6, 5, 2, 1, 3, 8, 7 ],
[ 4, 7, 2, 5, 8, 3, 6, 1 ],
[ 4, 1, 7, 8, 6, 3, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 4, 6, 5, 2, 1, 3, 8, 7 ],
[ 3, 8, 5, 2, 7, 4, 1, 6 ],
[ 3, 6, 8, 7, 1, 4, 2, 5 ]
],
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 6, 3, 5, 2, 4, 1, 7, 8 ]:
 Order := 192 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 2, 4, 8, 7, 3, 5, 1, 6 ],
[ 4, 8, 2, 5, 7, 3, 1, 6 ]
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
