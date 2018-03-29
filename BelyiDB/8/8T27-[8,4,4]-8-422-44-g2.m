s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T27-[8,4,4]-8-422-44-g2";
s`BelyiDBFilename := "8T27-[8,4,4]-8-422-44-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 7, 4, 1, 6, 3, 8, 5 ],
[ 7, 4, 1, 2, 3, 8, 5, 6 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 7, 4, 1, 6, 3, 8, 5 ],
\[ 7, 4, 1, 2, 3, 8, 5, 6 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 7, 4, 1, 6, 3, 8, 5 ],
\[ 7, 4, 1, 2, 3, 8, 5, 6 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 >) |
[ PermutationGroup<8 |  
\[ 2, 7, 4, 1, 6, 3, 8, 5 ],
\[ 7, 4, 1, 2, 3, 8, 5, 6 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 7, 4, 1, 6, 3, 8, 5 ],
[ 7, 4, 1, 2, 3, 8, 5, 6 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 7, 4, 1, 6, 3, 8, 5 ],
\[ 7, 4, 1, 2, 3, 8, 5, 6 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 7, 4, 1, 6, 3, 8, 5 ],
[ 3, 8, 5, 6, 7, 4, 1, 2 ],
[ 6, 7, 4, 1, 2, 3, 8, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 >) |
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 7, 4, 1, 6, 3, 8, 5 ],
[ 7, 4, 1, 2, 3, 8, 5, 6 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ]
],
[ PermutationGroup<8 |  
\[ 1, 2, 3, 8, 5, 6, 7, 4 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 64 > |
[ 2, 7, 8, 5, 6, 3, 4, 1 ],
[ 3, 8, 1, 2, 7, 4, 5, 6 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ]
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
