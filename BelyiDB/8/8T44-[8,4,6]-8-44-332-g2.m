s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T44-[8,4,6]-8-44-332-g2";
s`BelyiDBFilename := "8T44-[8,4,6]-8-44-332-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 3, 8, 6, 1, 7, 4, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 3, 8, 6, 1, 7, 4, 2 ]:
 Order := 384 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 3, 8, 6, 1, 7, 4, 2 ]:
 Order := 384 >) |
[ PermutationGroup<8 |  
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 3, 8, 6, 1, 7, 4, 2 ]:
 Order := 384 > |
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 3, 8, 6, 1, 7, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 3, 8, 6, 1, 7, 4, 2 ]:
 Order := 384 > |
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 5, 7, 4, 6, 1, 3, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 3, 8, 6, 1, 7, 4, 2 ]:
 Order := 384 > |
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 8, 3, 5, 2, 4, 7, 1, 6 ],
[ 8, 1, 7, 6, 4, 5, 3, 2 ]
],
[ PermutationGroup<8 |  
\[ 3, 5, 8, 6, 7, 1, 4, 2 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 3, 8, 6, 1, 7, 4, 2 ]:
 Order := 384 > |
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 2, 7, 8, 1, 6, 3, 4, 5 ],
[ 5, 3, 4, 2, 1, 7, 8, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 >) |
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 3, 5, 8, 6, 7, 1, 4, 2 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 3, 8, 6, 1, 7, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 7, 5, 4, 6, 3, 1, 8, 2 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 3, 4, 2, 1, 7, 8, 6 ]
],
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 7, 5, 8, 2, 3, 1, 4, 6 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 7, 4, 6, 1, 3, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 3, 5, 4, 2, 7, 1, 8, 6 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 5, 7, 8, 2, 1, 3, 4, 6 ]
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
