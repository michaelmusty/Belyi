s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T45-[6,6,4]-62-62-44-g2";
s`BelyiDBFilename := "8T45-[6,6,4]-62-62-44-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 4, 5, 7, 2, 8, 1, 3, 6 ],
[ 4, 7, 5, 3, 8, 1, 2, 6 ],
[ 8, 1, 2, 6, 7, 5, 4, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 5, 7, 2, 8, 1, 3, 6 ],
\[ 4, 7, 5, 3, 8, 1, 2, 6 ],
\[ 8, 1, 2, 6, 7, 5, 4, 3 ]:
 Order := 576 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 5, 7, 2, 8, 1, 3, 6 ],
\[ 4, 7, 5, 3, 8, 1, 2, 6 ],
\[ 8, 1, 2, 6, 7, 5, 4, 3 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 4, 5, 7, 2, 8, 1, 3, 6 ],
\[ 4, 7, 5, 3, 8, 1, 2, 6 ],
\[ 8, 1, 2, 6, 7, 5, 4, 3 ]:
 Order := 576 > |
[ 4, 5, 7, 2, 8, 1, 3, 6 ],
[ 4, 5, 6, 2, 3, 1, 8, 7 ],
[ 3, 1, 8, 6, 4, 7, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 5, 7, 2, 8, 1, 3, 6 ],
\[ 4, 7, 5, 3, 8, 1, 2, 6 ],
\[ 8, 1, 2, 6, 7, 5, 4, 3 ]:
 Order := 576 > |
[ 4, 5, 7, 2, 8, 1, 3, 6 ],
[ 5, 6, 4, 2, 3, 1, 8, 7 ],
[ 2, 3, 8, 6, 4, 7, 5, 1 ]
],
[ PermutationGroup<8 |  
\[ 4, 5, 7, 2, 8, 1, 3, 6 ],
\[ 4, 7, 5, 3, 8, 1, 2, 6 ],
\[ 8, 1, 2, 6, 7, 5, 4, 3 ]:
 Order := 576 > |
[ 4, 5, 7, 2, 8, 1, 3, 6 ],
[ 4, 5, 6, 3, 1, 2, 8, 7 ],
[ 3, 1, 8, 5, 6, 7, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 5, 7, 2, 8, 1, 3, 6 ],
\[ 4, 7, 5, 3, 8, 1, 2, 6 ],
\[ 8, 1, 2, 6, 7, 5, 4, 3 ]:
 Order := 576 > |
[ 4, 5, 7, 2, 8, 1, 3, 6 ],
[ 7, 6, 5, 8, 1, 3, 2, 4 ],
[ 2, 8, 1, 5, 7, 4, 6, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 4, 5, 7, 2, 8, 1, 3, 6 ],
[ 4, 7, 5, 3, 8, 1, 2, 6 ],
[ 8, 1, 2, 6, 7, 5, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 5, 4, 7, 8, 2, 1, 3, 6 ],
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 8, 1, 2, 6, 7, 5, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 4, 5, 7, 8, 2, 3, 1, 6 ],
[ 5, 6, 4, 3, 8, 1, 2, 7 ],
[ 8, 1, 2, 6, 7, 5, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 4, 5, 1, 3, 2, 8, 6 ],
[ 6, 5, 7, 1, 8, 2, 3, 4 ],
[ 8, 1, 2, 6, 7, 5, 4, 3 ]
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
