s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T24-[6,4,4]-62-44-44-g2";
s`BelyiDBFilename := "8T24-[6,4,4]-62-44-44-g2.m";
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
\[ 1, 3, 2, 5, 4, 6, 7, 8 ]:
 Order := 48 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 3, 8, 2, 5, 7, 4, 6, 1 ],
[ 5, 7, 6, 1, 8, 2, 3, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 3, 8, 2, 5, 7, 4, 6, 1 ],
\[ 5, 7, 6, 1, 8, 2, 3, 4 ]:
 Order := 48 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 3, 8, 2, 5, 7, 4, 6, 1 ],
\[ 5, 7, 6, 1, 8, 2, 3, 4 ]:
 Order := 48 >) |
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 3, 8, 2, 5, 7, 4, 6, 1 ],
\[ 5, 7, 6, 1, 8, 2, 3, 4 ]:
 Order := 48 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 3, 8, 2, 5, 7, 4, 6, 1 ],
[ 5, 7, 6, 1, 8, 2, 3, 4 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 3, 8, 2, 5, 7, 4, 6, 1 ],
\[ 5, 7, 6, 1, 8, 2, 3, 4 ]:
 Order := 48 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 5, 7, 6, 1, 8, 2, 3, 4 ],
[ 2, 3, 8, 7, 4, 5, 6, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 1, 3, 2, 5, 4, 6, 7, 8 ]:
 Order := 48 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 1, 3, 2, 5, 4, 6, 7, 8 ]:
 Order := 48 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 3, 8, 2, 5, 7, 4, 6, 1 ],
[ 5, 7, 6, 1, 8, 2, 3, 4 ]
],
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ],
\[ 1, 3, 2, 5, 4, 6, 7, 8 ]:
 Order := 48 > |
[ 7, 6, 4, 3, 1, 8, 2, 5 ],
[ 4, 6, 7, 8, 1, 3, 2, 5 ],
[ 8, 3, 1, 6, 4, 7, 5, 2 ]
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
