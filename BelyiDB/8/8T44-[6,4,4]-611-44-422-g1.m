s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T44-[6,4,4]-611-44-422-g1";
s`BelyiDBFilename := "8T44-[6,4,4]-611-44-422-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 384 > |
[ 7, 1, 2, 4, 3, 5, 6, 8 ],
[ 8, 7, 1, 2, 4, 3, 5, 6 ],
[ 4, 6, 7, 5, 8, 2, 3, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 1, 2, 4, 3, 5, 6, 8 ],
\[ 8, 7, 1, 2, 4, 3, 5, 6 ],
\[ 4, 6, 7, 5, 8, 2, 3, 1 ]:
 Order := 384 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 1, 2, 4, 3, 5, 6, 8 ],
\[ 8, 7, 1, 2, 4, 3, 5, 6 ],
\[ 4, 6, 7, 5, 8, 2, 3, 1 ]:
 Order := 384 >) |
[ PermutationGroup<8 |  
\[ 7, 1, 2, 4, 3, 5, 6, 8 ],
\[ 8, 7, 1, 2, 4, 3, 5, 6 ],
\[ 4, 6, 7, 5, 8, 2, 3, 1 ]:
 Order := 384 > |
[ 7, 1, 2, 4, 3, 5, 6, 8 ],
[ 8, 7, 1, 2, 4, 3, 5, 6 ],
[ 4, 6, 7, 5, 8, 2, 3, 1 ]
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
[ 7, 1, 2, 4, 3, 5, 6, 8 ],
[ 8, 7, 1, 2, 4, 3, 5, 6 ],
[ 4, 6, 7, 5, 8, 2, 3, 1 ]
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
