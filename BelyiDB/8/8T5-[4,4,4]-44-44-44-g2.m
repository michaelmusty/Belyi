s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T5-[4,4,4]-44-44-44-g2";
s`BelyiDBFilename := "8T5-[4,4,4]-44-44-44-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 6, 5, 2, 1, 8, 3, 4 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 7, 6, 3, 2, 1, 8, 5 ],
[ 7, 6, 5, 2, 1, 8, 3, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 8, 1, 2, 5, 6, 7, 4, 3 ],
\[ 7, 4, 5, 8, 1, 2, 3, 6 ]:
 Order := 8 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 7, 4, 5, 6, 1 ]:
 Order := 4 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 7, 6, 3, 2, 1, 8, 5 ],
\[ 7, 6, 5, 2, 1, 8, 3, 4 ]:
 Order := 8 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 7, 6, 3, 2, 1, 8, 5 ],
\[ 7, 6, 5, 2, 1, 8, 3, 4 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 7, 6, 3, 2, 1, 8, 5 ],
\[ 7, 6, 5, 2, 1, 8, 3, 4 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 7, 6, 3, 2, 1, 8, 5 ],
[ 7, 6, 5, 2, 1, 8, 3, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 6, 5, 2, 1, 8, 3, 4 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 6, 5, 2, 1, 8, 3, 4 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 7, 6, 3, 2, 1, 8, 5 ],
[ 7, 6, 5, 2, 1, 8, 3, 4 ]
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
